%%%-------------------------------------------------------------------
%% @doc 2bdb top level supervisor.
%% @end
%%%-------------------------------------------------------------------

-module('2bdb_sup').

-behaviour(supervisor).

%% API
-export([start_link/0]).

%% Supervisor callbacks
-export([init/1]).

-define(SERVER, ?MODULE).

%%====================================================================
%% API functions
%%====================================================================

start_link() ->
  supervisor:start_link({local, ?SERVER}, ?MODULE, []).

%%====================================================================
%% Supervisor callbacks
%%====================================================================

init([]) ->
  SupFlags = {one_for_all, 0, 1},
  NumPartitions = application:get_env('2bdb', num_partitions, 1),
  PartitionWorkers = [worker(I) || I <- lists:seq(0, NumPartitions - 1)],
  {ok, {SupFlags, PartitionWorkers}}.

%%====================================================================
%% Internal functions
%%====================================================================

worker(Partition) ->
  #{ id => Partition
   , start => {'2bdb_partition_worker', start_link, [Partition]}
   }.
