-module(system_test_SUITE).

-compile(export_all).

-on_init(suite/0).

-include_lib("hut/include/hut.hrl").
-include_lib("snabbkaffe/include/ct_boilerplate.hrl").

-define(kafka_endpoint, [{"localhost", 9092}]).

%%====================================================================
%% CT callbacks
%%====================================================================

suite() ->
  application:load(snabbkaffe),
  [{timetrap, {seconds, 180}}].

init_per_suite(Config) ->
  snabbkaffe:fix_ct_logging(),
  %% Dir = code:lib_dir('2bdb'),
  %% Out = os:cmd(filename:join([Dir, "test", "setup-test-env.sh"])),
  %% ?log(info, "~s", [["Docker output:\n", Out]]),
  Config.

end_per_suite(_Config) ->
  ok.

init_per_group(_GroupName, Config) ->
  Config.

end_per_group(_GroupName, _Config) ->
  ok.

groups() ->
  [].

%%====================================================================
%% Testcases
%%====================================================================

t_counter({init, Config}) ->
  common_startup(?FUNCTION_NAME, Config);
t_counter({'end', Config}) ->
  common_stop();
t_counter(Config) ->
  {ok, _} = application:ensure_all_started('2bdb').

%%====================================================================
%% Internal functions
%%====================================================================

common_stop() ->
  application:stop('2bdb'),
  application:stop(brod),
  application:stop(rocksdb).

common_startup(TestCase, Config) ->
  NumPartitions = 1,
  Topic = atom_to_binary(TestCase, latin1),
  application:set_env('2bdb', kafka_endpoints, ?kafka_endpoint),
  application:set_env('2bdb', num_partitions, NumPartitions),
  application:set_env('2bdb', tlog_topic, Topic),
  ?retry(1000, 120, create_topic(Topic, NumPartitions)),
  Config.

create_topic(Name, NumPartitions) ->
  TopicFields = [ {topic, Name}
                , {num_partitions, NumPartitions}
                , {replication_factor, 1}
                , {replica_assignment, []}
                , {config_entries, [[ {config_name,"max.message.bytes"}
                                    , {config_value, "20485760"}
                                    ]]}
                ],
  Req = kpro_req_lib:create_topics( 0
                                  , [TopicFields]
                                  , #{timeout => 5000}
                                  ),
  {ok, Conn} = kpro:connect_any(?kafka_endpoint, []),
  {ok, _Res} = kpro:request_sync(Conn, Req, 5000),
  kpro:close_connection(Conn).
