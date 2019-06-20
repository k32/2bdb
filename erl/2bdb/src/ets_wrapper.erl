-module(ets_wrapper).

-export([create_table/1, put/1]).

create_table(Tab) ->
  case ets:info(Tab) of
    undefined ->
      ets:new(Tab, [named_table, public]);
    _ ->
      ok
  end.

put(WriteOps) ->
  [ets:insert(Tab, {Key, Val}) || {{Tab, Key}, Val} <- WriteOps],
  ok.
