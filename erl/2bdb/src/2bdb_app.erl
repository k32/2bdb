%%%-------------------------------------------------------------------
%% @doc 2bdb public API
%% @end
%%%-------------------------------------------------------------------

-module('2bdb_app').

-behaviour(application).

%% Application callbacks
-export([start/2, stop/1]).

-include("2bdb_int.hrl").

%%====================================================================
%% API
%%====================================================================

start(_StartType, _StartArgs) ->
  start_brod_client(),
  '2bdb_sup':start_link().

%%--------------------------------------------------------------------
stop(_State) ->
  ok.

%%====================================================================
%% Internal functions
%%====================================================================

start_brod_client() ->
  Kafka = application:get_env( '2bdb'
                             , kafka_endpoints
                             , [{"localhost", 9092}]
                             ),
  ok = brod:start_client(Kafka, ?brod_client).
