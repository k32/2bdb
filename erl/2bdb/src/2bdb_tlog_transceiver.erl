-module('2bdb_tlog_transceiver').

%% TODO: Currently this module does not handle kafka errors whatsoever

-behavior(brod_topic_subscriber).

-include_lib("brod/include/brod.hrl").
-include("2bdb_int.hrl").

-define(chunk_cnt, <<42>>).
-define(chunk_num, <<41>>).

% API:
-export([ subscribe_partition/1
        , produce/3
        ]).

% Brod callbacks:
-export([ init/2
        , handle_message/3
        ]).

%%%===================================================================
%%% Types
%%%===================================================================

-type wait_ref() :: [brod:call_ref()].

-record(chunk,
        { begin_offset :: non_neg_integer()
        , last_chunk   :: non_neg_integer()
        , data         :: binary()
        }).

-type chunks() :: #{reference() => #chunk{}}.

-record(s,
        { chunks = #{} :: chunks()
        , offset       :: non_neg_integer()
        , worker       :: pid()
        }).

-define(get_topic,
        application:get_env('2bdb', tlog_topic, <<"2bdb.tlog">>)).

%%%===================================================================
%%% API
%%%===================================================================

-spec subscribe_partition(integer()) -> {ok, pid()}.
subscribe_partition(Partition) ->
  Topic = ?get_topic,
  MaxWaitTime = application:get_env('2bdb', tlog_buffer_time, 10),
  Config = [{max_wait_time, MaxWaitTime}],
  CommitedOffsets = [{Partition, earliest}],
  brod_topic_subscriber:start_link( '2bdb_client'
                                  , Topic
                                  , [Partition]
                                  , Config
                                  , ?MODULE
                                  , {Partition, self()}
                                  ).

-spec produce(reference(), integer(), term()) -> {ok, wait_ref()}.
produce(Ref, Partition, Term) ->
  Topic = ?get_topic,
  ChunkSize = application:get_env('2bdb', tlog_chunk_size, 1 bsl 19),
  Bin = term_to_binary(Term),
  if byte_size(Bin) < ChunkSize ->
      {ok, WaitRef} = brod:produce( ?brod_client
                                  , Topic
                                  , Partition
                                  , <<>>
                                  , Bin
                                  ),
      {ok, [WaitRef]};
     true ->
      Key = term_to_binary(Ref),
      {Parts, ChunkCnt} = chop(Bin, ChunkSize),
      WaitRef =
        [begin
           Msg = #{ headers => [ {?chunk_cnt, <<ChunkCnt:32>>}
                               , {?chunk_num, <<N:32>>}
                               ]
                  , value   => Data
                  },
           {ok, Ref} = brod:produce( ?brod_client
                                   , Topic
                                   , Partition
                                   , Key
                                   , Msg
                                   ),
           Ref
         end
         || {N, Data} <- lists:zip( lists:seq(1, ChunkCnt)
                                  , Parts
                                  )],
      {ok, WaitRef}
  end.

%%%===================================================================
%%% Brod callbacks
%%%===================================================================

init(Topic, {Partition, Pid}) ->
  Offset = 0, %% TODO
  State = #s{ offset = Offset
            , worker = Pid
            },
  {ok, [{Partition, Offset}], State}.

handle_message( _Partition
              , #kafka_message{ offset = Offset
                              , value = Value
                              , key = Key
                              , headers = Headers
                              }
              , State0 = #s{ chunks = Chunks0
                           , worker = Pid
                           }
              ) ->
  case Key of
    <<>> ->
      %% Key is empty: this message is a singleton
      Msg = binary_to_term(Value),
      '2bdb_partition_worker':import_tlog(Pid, Offset, Msg),
      Chunks = Chunks0;
    _ ->
      {_, <<ChunkCnt:32>>} = lists:keyfind(?chunk_cnt, 1, Headers),
      {_, <<ChunkNum:32>>} = lists:keyfind(?chunk_num, 1, Headers),
      Chunks = process_chunk( Pid
                            , Key
                            , Offset
                            , ChunkCnt
                            , ChunkNum
                            , Value
                            , Chunks0
                            )
  end,
  _SafeOffset = safe_offset(Offset, Chunks),
  State = State0#s{chunks = Chunks},
  {ok, State}.

-spec process_chunk( pid()
                   ,  Key :: binary()
                   , non_neg_integer()
                   , non_neg_integer()
                   , non_neg_integer()
                   , binary()
                   , chunks()
                   ) -> chunks().
process_chunk(Pid, Key, Offset, ChunkCnt, 0, Value, Chunks) ->
  %% First chunk in the series:
  Chunk = #chunk{ begin_offset = Offset
                , last_chunk   = 0
                , data         = Value
                },
  Chunks #{Key => Chunk};
process_chunk(Pid, Key, Offset, ChunkCnt, ChunkNum, Value, Chunks0) ->
  case Chunks0 of
    #{Key := Chunk0} ->
      #chunk{ data       = Data
            , last_chunk = LastChunk
            } = Chunk0,
      if ChunkNum =:= ChunkCnt, LastChunk =:= ChunkNum - 1 ->
          %% Last chunk in the complete series:
          Msg = binary_to_term(<<Data/binary, Value/binary>>),
          '2bdb_partition_worker':import_tlog(Pid, Offset, Msg),
          maps:without([Key], Chunks0);
         LastChunk =:= ChunkNum - 1 ->
          %% Valid continuation of the series:
          Chunk = Chunk0#chunk{data = <<Data/binary, Value/binary>>},
          Chunks0 #{Key => Chunk};
         true ->
          ?tp(warning, 'tlog_chunks_out_of_sequence',
              #{ cnt    => ChunkCnt
               , num    => ChunkNum
               , key    => Key
               , offset => Offset
               }),
          Chunks0
      end;
    _ ->
      %% Retransmission of an already processed key
      ?tp(warning, 'tlog_chunks_out_of_sequence',
          #{ cnt    => ChunkCnt
           , num    => ChunkNum
           , key    => Key
           , offset => Offset
           }),
      Chunks0
  end.

-spec safe_offset(integer(), chunks()) -> integer().
safe_offset(Offset, Chunks) ->
  Offsets = [O || {_, #chunk{begin_offset = O}} <- maps:to_list(Chunks)],
  lists:min([Offset|Offsets]).

-spec chop(binary(), non_neg_integer()) -> {[binary()], integer()}.
chop(Bin, ChunkSize) ->
  Chop = fun
           F(Chunk, {Acc, N}) when
               byte_size(Chunk) =< ChunkSize ->
             {[Chunk|Acc], N + 1};
           F(Bin, {Acc, N}) ->
             <<Chunk:ChunkSize/binary, Rest/binary>> = Bin,
             F(Rest, {[Chunk|Acc], N + 1})
         end,
  {Chunks, Length} = Chop(Bin, {[], 0}),
  {lists:reverse(Chunks), Length}.
