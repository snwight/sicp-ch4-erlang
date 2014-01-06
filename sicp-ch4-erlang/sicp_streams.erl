%%%-------------------------------------------------------------------
%%% @author Steve Wight <northwight@gmail.com>
%%% @copyright (C) 2014, Steve Wight
%%% @doc
%%%
%%% @end
%%% Created :  2 Jan 2014 by Steve Wight
%%%-------------------------------------------------------------------
-module(sicp_streams).

-include("sicp_streams.hrl").

%% handrolled implementation of delay/force - translated from scheme
delay(Exp) -> fun() -> Exp end.
force(Promise) -> Promise.

%% (cons-stream <a> <b>) ====> (cons <a> (delay <b>))
cons_stream(Car, Cdr) -> [Car|delay(Cdr)].
 
stream_car([Car|_]) -> Car.
stream_cdr([_|Cdr]) -> force(Cdr).

is_stream_null([]) -> true;
is_stream_null(_) -> false.

list_to_stream(List) -> List.

stream_map(Proc, S) ->
    case is_stream_null(S) of
	true -> ?THE_EMPTY_STREAM;
	false -> cons_stream(Proc(stream_car(S)), 
			     stream_map(Proc, stream_cdr(S)))
    end.

stream_for_each(Proc, S) ->
    case is_stream_null(S) of
	true -> done;
	false ->
	    Proc(stream_car(S)),
	    stream_for_each(Proc, stream_cdr(S))
    end.

display_stream(S) -> 
    stream_for_each(fun display_line/1, S).

display_line(X) -> 
    io:format("~n~s", [X]).

stream_filter(Pred, Stream) ->
   case is_stream_null(Stream) of
       true -> ?THE_EMPTY_STREAM;
       false -> 
	   case Pred(stream_car(Stream)) of
	       true -> cons_stream(stream_car(Stream),
				   stream_filter(Pred, stream_cdr(Stream)));
	       false -> stream_filter(Pred, stream_cdr(Stream))
	   end
   end.

stream_append(S1, S2) ->
    case is_stream_null(S1) of
	true -> S2;
	false -> cons_stream(stream_car(S1), 
			     stream_append(stream_cdr(S1), S2))
    end.

interleave(S1, S2) ->
    case is_stream_null(S1) of
	true -> s2;
	false -> cons_stream(stream_car(S1), 
			     interleave(S2, stream_cdr(S1)))
    end.

stream_append_delayed(S1, Delayed_S2) ->
    case is_stream_null(S1) of
	true -> force(Delayed_S2);
	false -> cons_stream(stream_car(S1),
			     stream_append_delayed(
			       stream_cdr(S1), Delayed_S2))
    end.

interleave_delayed(S1, Delayed_S2) ->
    case is_stream_null(S1) of
	true -> force(Delayed_S2);
	false -> cons_stream(stream_car(S1),
			     interleave_delayed(
			       force(Delayed_S2),
			       delay(stream_cdr(S1))))
    end.

stream_flatmap(Proc, S) ->
    flatten_stream(stream_map(Proc, S)).

flatten_stream(Stream) ->
    case is_stream_null(Stream) of
	true -> ?THE_EMPTY_STREAM;
	false -> interleave_delayed(
		   stream_car(Stream),
		   delay(flatten_stream(stream_cdr(Stream))))
    end.

singleton_stream(X) -> cons_stream(X, ?THE_EMPTY_STREAM).

