-module('2bdb_partition_worker').

-behavior(gen_statem).

-include_lib("stdlib/include/assert.hrl").
-include_lib("snabbkaffe/include/snabbkaffe.hrl").
-include_lib("hut/include/hut.hrl").

-define(TabHashBits, 16).

%% API
-export([ start_link/1
        , try_write_trans/3
        , import_tlog/3
        ]).

%% gen_statem callbacks
-export([callback_mode/0, init/1, terminate/3, code_change/4]).
-export([handle_event/4]).

-define(SERVER, ?MODULE).

%%%===================================================================
%%% Types
%%%===================================================================

%%--------------------------------------------------------------------
%% Replication protocol:
%%--------------------------------------------------------------------

-type partition() :: integer().

-type txid() :: reference().

-type key() :: {Table :: atom(), _Key}.

-type key_hash() :: binary().

-type seqno() :: non_neg_integer().

-type read_ops() :: [{key_hash(), seqno()}].

-type write_ops() :: [{key(), seqno(), _Value}].

-type offset() :: non_neg_integer().

-type tx_result() :: atomic
                   | retry
                   | aborted
                   .

-record(tx,
        { id               :: txid()
        , estimated_offset :: offset()
        , partitions       :: [partition()] %% Partitions (excluding the current one)
                                            %% containing other parts of the transaction
        , reads            :: read_ops()
        , writes           :: write_ops()
        }).

-type tx() :: #tx{}.

-type schema_tx() :: {create_table, atom()}.

%% Note: these changes don't apply retroactively
-type meta_op() :: {set_repl_params,
                    #{ window_size     := non_neg_integer()
                     , lock_expiration := non_neg_integer()
                     }}.

-type lock_op() :: {grab_locks, txid(), [key_hash()]}
                 | {keep_locks, txid()}
                 .

-type tlog_op() :: meta_op()
                 | lock_op()
                 | tx()
                 | schema_tx()
                 .

%%--------------------------------------------------------------------
%% Internal types:
%%--------------------------------------------------------------------

-type state() :: incomplete_window
               | behind              %% TODO not implemented
               | hold_on             %% TODO not implemented
               | in_sync
               .

-type os_timestamp() :: integer().

-type producer() :: term().

-type consumer() :: term().

-record(try_write_trans,
        { id       :: txid()
        , ts_begin :: os_timestamp() %% For performance measurements only
        , reads    :: [key_hash()]
        , writes   :: [{key(), _Value}]
        }).

-record(data,
        { storage = ets_wrapper :: module()
        , my_partition          :: partition()
        , window_size     = 1   :: non_neg_integer()
        , lock_expiration = 0   :: non_neg_integer()
        , num_replayed    = 0   :: non_neg_integer()
        , offset          = 0   :: offset()
        , seqno_tab             :: ets:tid()
        , callback_tab          :: ets:tid()
        , producer_data         :: producer()
        , consumer              :: consumer()
        }).

-type data() :: #data{}.

-record(seqno_cache,
        { key              :: key_hash()
        , seqno            :: seqno()
        , last_seen_offset :: offset()
        }).

-record(callback_ref,
        { txid             :: txid()
        , reply_to         :: gen_statem:from()
        , estimated_offset :: offset() %% This offset should not be very precise,
                                       %% it's used only for hangup detection
        , ts_begin         :: os_timestamp()
        }).

%%%===================================================================
%%% API
%%%===================================================================

%%--------------------------------------------------------------------
%% @doc
%% Creates a gen_statem process which calls Module:init/1 to
%% initialize. To ensure a synchronized start-up procedure, this
%% function does not return until Module:init/1 has returned.
%%
%% @end
%%--------------------------------------------------------------------
-spec start_link(partition()) -> {ok, Pid :: pid()}.
start_link(Partition) ->
  gen_statem:start_link(?MODULE, [Partition], []).

-spec try_write_trans(pid(), boolean(), #try_write_trans{}) -> tx_result().
try_write_trans(Pid, GrabLock, Tx) ->
  ?tp('2bdb_enter_write_trans', #{ txid => Tx#try_write_trans.id
                                 }),
  gen_statem:call(Pid, Tx).

-spec import_tlog(pid(), offset(), tlog_op()) -> ok.
import_tlog(Pid, Offset, TLOG) ->
  gen_statem:call(Pid, {import_tlog, Offset, TLOG}).

%%%===================================================================
%%% gen_statem callbacks
%%%===================================================================

-spec callback_mode() -> gen_statem:callback_mode_result().
callback_mode() -> handle_event_function.

-spec init([partition()]) ->
                  gen_statem:init_result(term()).
init([Partition]) ->
  process_flag(trap_exit, true),
  Consumer    =
  SeqNoTab    = ets:new( '2bdb_seqno_tab'
                       , [ {keypos, #seqno_cache.key}
                         , protected
                         , named_table
                         ]
                       ),
  CallbackTab = ets:new( '2bdb_callback_tab'
                       , [{keypos, #callback_ref.txid}]
                       ),
  InitialData = #data{ seqno_tab    = SeqNoTab
                     , callback_tab = CallbackTab
                     , my_partition = Partition
                     , consumer     = Consumer
                     },
  %% TODO: read persisted data
  Data = InitialData,
  {ok, incomplete_window, Data}.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% This function is called for every event a gen_statem receives.
%% @end
%%--------------------------------------------------------------------
%% Handle data from the topic:
handle_event({call, From}, {import_tlog, Offset, TLOG}, State, Data) ->
  Ret = handle_tlog(State, Data, TLOG),
  gen_statem:reply(From, ok),
  Ret;
%% Handle local transactions:
handle_event({call, From}, Tx = #try_write_trans{}, in_sync, Data) ->
  %% We are ready to write transactions:
  do_write_trans(Data, From, Tx);
handle_event({call, _}, #try_write_trans{}, hold_on, _Data) ->
  %% We need to back off. Queue up this transaction for now
  {keep_state_and_data, [postpone]};
handle_event({call, From}, #try_write_trans{}, _State, _Data) ->
  %% We need to back off. Queue up this transaction for now
  {keep_state_and_data, [{reply, From, {error, write_not_allowed}}]};
handle_event({call, From}, #try_write_trans{}, _State, _Data) ->
  %% TODO: not the best solution... Will cause busy loop
  %% 1) Forward tx to a different host
  %%
  %% 2) or postpone the transaction and check the offset: if offset
  %% difference is too large, drop the tx
  {keep_state_and_data, [{reply, From, retry}]};
%% Common actions:
handle_event({call, From}, EvtData, State, _Data) ->
  ?slog(error, #{ what => "Unknown call"
                , data => EvtData
                , current_state => State
                }),
  Reply = {error, unknown_call},
  {keep_state_and_data, [{reply, From, Reply}]};
handle_event(Event, EvtData, State, _Data) ->
  ?slog(error, #{ what => "Unknown event"
                , type => Event
                , data => EvtData
                , current_state => State
                }),
  keep_state_and_data.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% Handle message from TLOG
%% @end
%%--------------------------------------------------------------------
-spec handle_tlog(tlog_op(), state(), data()) ->
        gen_statem:event_handler_result(state()).
handle_tlog({set_repl_params, Params}, _State, Data0) ->
  %% TODO: This entire code is sketchy
  #{ window_size     := WS
   , lock_expiration := LI
   } = Params,
  Data = Data0#data{ window_size     = WS
                   , lock_expiration = LI
                   },
  {keep_state, Data};
%% Handle schema transactions:
handle_tlog({import_schema_trans, Tx}, _State, Data) ->
  handle_schema_transaction(Data, Tx),
  keep_state_and_data;
%% Handle import transaction:
handle_tlog({import_trans, TrueOffset, Tx}, OldState, Data0) ->
  Data = handle_import_transaction(Data0, TrueOffset, Tx),
  #data{ num_replayed = NumImported
       , window_size  = WindowSize
       } = Data,
  NextState = if NumImported >= WindowSize,
                 OldState =:= incomplete_window ->
                  in_sync;
                 true ->
                  OldState
              end,
  {next_state, NextState, Data}.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% This function is called by a gen_statem when it is about to
%% terminate. It should be the opposite of Module:init/1 and do any
%% necessary cleaning up. When it returns, the gen_statem terminates with
%% Reason. The return value is ignored.
%% @end
%%--------------------------------------------------------------------
-spec terminate(_Reason, _State, _Data) -> any().
terminate(_Reason, _State, _Data) ->
  void.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% Convert process state when code is changed
%% @end
%%--------------------------------------------------------------------
-spec code_change(
        OldVsn :: term() | {down,term()},
        State :: term(), Data :: term(), Extra :: term()) ->
                         {ok, NewState :: term(), NewData :: term()} |
                         (Reason :: term()).
code_change(_OldVsn, State, Data, _Extra) ->
  {ok, State, Data}.

%%%===================================================================
%%% Internal functions
%%%===================================================================

-spec do_write_trans( data()
                    , gen_statem:from()
                    , #try_write_trans{}
                    ) -> keep_state_and_data.
do_write_trans(Data, From, Tx) ->
  #data{ seqno_tab    = SeqNoTab
       , callback_tab = CallbackTab
       , offset       = Offset
       } = Data,
  #try_write_trans{ id       = Txid
                  , ts_begin = TsBegin
                  , reads    = Reads
                  , writes   = Writes
                  } = Tx,
  ReadOps = [{KeyHash, get_seqno(Data, KeyHash)} || KeyHash <- Reads],
  WriteOps = [{Key, get_seqno(Data, key_hash(Key)), Val}
              || {Key, Val} <- Writes],
  %% Produce transaction to the tlog (asynchronously, because we are
  %% that optimistic!):
  produce(Data, #tx{ id               = Txid
                   , partitions       = []   %% TODO: Chop it up
                   , reads            = ReadOps
                   , writes           = WriteOps
                   , estimated_offset = Offset
                   }),
  %% Write transaction reference to the callback buffer:
  ets:insert( CallbackTab
            , #callback_ref{ txid             = Txid
                           , reply_to         = From
                           , estimated_offset = Offset
                           , ts_begin         = TsBegin
                           }
            ),
  %% Don't reply yet:
  keep_state_and_data.

-spec handle_import_transaction(data(), offset(), tx()) -> data().
handle_import_transaction(Data0, TrueOffset, Tx) ->
  #data{ window_size  = WindowSize
       , num_replayed = NumReplayed
       } = Data0,
  #tx{ id               = TxId
     , estimated_offset = EstimatedOffset
     , writes           = WriteOps
     , reads            = ReadOps
     } = Tx,
  ?assert(EstimatedOffset =< TrueOffset),
  WriteSeqNos = [{key_hash(Key), SeqNo}
                 || {Key, SeqNo, _} <- WriteOps],
  Valid = (TrueOffset - EstimatedOffset < WindowSize) andalso
          validate_locks(Data0, WriteOps) andalso
          validate_seqnos(Data0, WriteSeqNos) andalso
          validate_seqnos(Data0, ReadOps),
  Data = Data0#data{ offset       = TrueOffset
                   , num_replayed = NumReplayed + 1
                   },
  if Valid ->
      do_import_transaction(Data, WriteOps),
      maybe_complete_transaction(Data, TxId, atomic);
     true ->
      maybe_complete_transaction(Data, TxId, retry)
  end,
  Data.

-spec handle_schema_transaction(data(), schema_tx()) -> ok.
handle_schema_transaction(Data, {create_table, Table}) ->
  '2bdb_storage':create_table(Table).

-spec get_seqno(data(), key_hash()) -> seqno().
get_seqno(Data, KeyHash) ->
  #data{ seqno_tab   = Tab
       , window_size = WindowSize
       , offset      = Offset
       } = Data,
  case ets:lookup(Tab, KeyHash) of
    [#seqno_cache{seqno = N, last_seen_offset = LSO}]
      when Offset - LSO < WindowSize ->
      LSO;
    _ ->
      0
  end.

-spec do_import_transaction(data(), write_ops()) -> ok.
do_import_transaction(Data, WriteOps) ->
  '2bdb_storage':put([{Key, Val} || {Key, _, Val} <- WriteOps]),
  bump_seqnos(Data, WriteOps).

-spec bump_seqnos(data(), write_ops()) -> ok.
bump_seqnos(Data, WriteOps) ->
  #data{ seqno_tab   = SeqNoTab
       , offset      = Offset
       , storage     = Storage
       , window_size = WindowSize
       } = Data,
  Inserts = [#seqno_cache{ key              = key_hash(Key)
                         , seqno            = (OldSeqNo + 1) rem WindowSize
                         , last_seen_offset = Offset
                         }
             || {Key, OldSeqNo, _} <- WriteOps],
  ets:insert(SeqNoTab, Inserts),
  ok.

-spec validate_locks(data(), write_ops()) -> boolean().
validate_locks(Data, WriteOps) ->
    %% TODO: Not implemented
    true.

-spec validate_seqnos(data(), [{key_hash(), seqno()}]) -> boolean().
validate_seqnos(Data, SeqNos) ->
  try
    [case get_seqno(Data, KeyHash) of
       ExpectedSeqNo -> ok;
       TrueSeqNo     -> throw(mismatch)
     end
     || {KeyHash, ExpectedSeqNo} <- SeqNos],
    true
  catch
    mismatch -> false
  end.

%% Signal `Result' to the transaction process
-spec maybe_complete_transaction(data(), txid(), tx_result()) -> ok.
maybe_complete_transaction(Data, TxId, Result) ->
  #data{callback_tab = Tab} = Data,
  case ets:take(Tab, TxId) of
    [#callback_ref{reply_to = From}] ->
      ?tp('tx_import_complete', #{ txid   => TxId
                                 , result => Result
                                 }),
      gen_statem:reply(From, Result);
    [] ->
      %% This transaction didn't originate from our server,
      %% ignore it.
      ok
  end.

-spec produce(data(), tlog_op()) -> ok.
produce(#data{producer_data = ProducerData}, Op) ->
  %% TODO: Not implemented
  ok.

-spec key_hash(key()) -> key_hash().
key_hash({Tab, Key}) ->
  %% TODO: Probably not optimal. This algorithm should be chosen
  %% wisely, as changing it later may become a problem
  <<TabHash:?TabHashBits, _/binary>> = erlang:md5(term_to_binary(Tab)),
  <<_:?TabHashBits, KeyHash/binary>> = erlang:md5(term_to_binary(Key)),
  <<TabHash:?TabHashBits, KeyHash/binary>>.
