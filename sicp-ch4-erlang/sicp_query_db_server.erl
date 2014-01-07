%%%-------------------------------------------------------------------
%%% @author Steve Wight <northwight@gmail.com>
%%% 
%%% @doc
%%%
%%% @end
%%% Created :  1 Jan 2014 by Steve Wight <northwight@gmail.com>
%%%-------------------------------------------------------------------
-module(sicp_query_db_server).

-behaviour(gen_server).

%% API
-export([start_link/0]).

%% gen_server callbacks
-export([init/1, handle_call/3, handle_cast/2, handle_info/2,
	 terminate/2, code_change/3]).

-define(SERVER, ?MODULE).

-record(state, {rules=[], assertions=[]}).

%%%===================================================================
%%% API
%%%===================================================================
get(Key1, Key2) ->
    gen_server:call(sicp_query_db, {get, {Key1, Key2}}).
put(Key1, Key2, Value) ->
    gen_server:call(sicp_query_db, {put, {Key1, Key2, Value}}).
fetch_rules(Pattern) ->
    gen_server:call(sicp_query_db, {fetch_rules, Pattern}).
fetch_assertions(Pattern) ->
    gen_server:call(sicp_query_db, {fetch_assertions, Pattern}).
add_rule_or_assertion(Decl) ->
    gen_server:call(sicp_query_db, {add_rule_or_assertion, Decl}).

%%--------------------------------------------------------------------
%% @doc
%% Starts the server
%%
%% @spec start_link() -> {ok, Pid} | ignore | {error, Error}
%% @end
%%--------------------------------------------------------------------
start_link() ->
    gen_server:start_link({local, ?SERVER}, ?MODULE, [], []).

%%%===================================================================
%%% gen_server callbacks
%%%===================================================================

%%--------------------------------------------------------------------
%% @private
%% @doc
%% Initializes the server
%%
%% @spec init(Args) -> {ok, State} |
%%                     {ok, State, Timeout} |
%%                     ignore |
%%                     {stop, Reason}
%% @end
%%--------------------------------------------------------------------
init([Rules_and_assertions]) ->
    {RuleStream, AssertionStream} = initialize_data_base(Rules_and_assertions),
    {ok, #state{rules=RuleStream, assertions=AssertionStream}}.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% Handling call messages
%%
%% @spec handle_call(Request, From, State) ->
%%                                   {reply, Reply, State} |
%%                                   {reply, Reply, State, Timeout} |
%%                                   {noreply, State} |
%%                                   {noreply, State, Timeout} |
%%                                   {stop, Reason, Reply, State} |
%%                                   {stop, Reason, State}
%% @end
%%--------------------------------------------------------------------
handle_call({fetch_rules, Pattern}, _From, State) ->
    S2 = case get_indexed_rules(Pattern) of
	     [] -> State;
	     Rules -> State#state{rules=Rules}
	 end,
    {reply, State#state.rules, S2};
handle_call({fetch_assertions, Pattern}, _From, State) ->
    S2 = case get_indexed_assertions(Pattern) of
	     [] -> State;
	     Assertions -> State#state{assertions=Assertions}
	 end,
    {reply, State#state.assertions, S2};
handle_call({add_rule_or_assertion, Decl}, _From, State) ->
    S2 = case is_rule(Decl) of
	     true -> 
		 store_rule_in_index(Decl),
		 R = sicp_streams:cons_stream(Decl, State#state.rules),
		 State#state{rules=R};
	     false -> 
		 store_assertion_in_index(Decl),
		 A = sicp_streams:cons_stream(Decl, State#state.assertions),
		 State#state{assertions=A}
	 end,
    {reply, ok, S2};
handle_call({get, {Key1, Key2}}, _From, State) ->
    qget(Key1, Key2),
    {reply, ok, State};
handle_call({put, {Key1, Key2, Value}}, _From, State) ->
    qput(Key1, Key2, Value),
    {reply, ok, State};
handle_call(_Request, _From, State) ->
    {reply, ok, State}.

%%--------------------------------------------------------------------
%% @private
%% @doc
%% @spec handle_cast(Msg, State) -> {noreply, State} |
%%                                  {noreply, State, Timeout} |
%%                                  {stop, Reason, State}
%% @end
%%--------------------------------------------------------------------
handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(_Info, State) ->
    {noreply, State}.
terminate(_Reason, _State) ->
    ok.
code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%%===================================================================
%%% Internal functions
%%%===================================================================
make_table() -> ets:new(q_tab, [bag, named_table, protected]).

qget(Key1, Key2) ->
    case ets:match(q_tab, {Key1, {Key2, '$0'}}) of
	[[Value]] -> Value;
	false -> false
    end.

qput(Key1, Key2, Value) -> 
    ets:insert(q_tab, {Key1, {Key2, Value}}).

initialize_data_base(Rules_and_assertions) ->
    make_table(),
    qput('and', 'qeval', conjoin),
    qput('or', 'qeval', disjoin),
    qput('not', 'qeval', negate),
    qput('lisp-value', 'qeval', lisp_value),
    qput('always-true', 'qeval', always_true),
    deal_out(Rules_and_assertions, [], []).

deal_out([], Rules, Assertions) ->
    {sicp_streams:list_to_stream(Assertions), 
     sicp_streams:list_to_stream(Rules)};
deal_out([Car|Cdr], Rules, Assertions) ->
    S = sicp_query_server:query_syntax_process(Car),
    case is_rule(S) of
	true ->
	    store_rule_in_index(S),
	    deal_out(Cdr, [S|Rules], Assertions);
	false ->
	    store_assertion_in_index(S),
	    deal_out(Cdr, Rules, [S|Assertions])
    end.

get_indexed_assertions(Pattern) ->
    get_stream(index_key_of(Pattern), assertion_stream).

get_stream(Key1, Key2) -> get(Key1, Key2).

get_indexed_rules(Pattern) ->
    sicp_streams:stream_append(
      get_stream(index_key_of(Pattern), rule_stream),
      get_stream('?', rule_stream)).

store_assertion_in_index(Assertion) ->
    case is_indexable(Assertion) of
	true ->
	    Key = index_key_of(Assertion),
	    Current_assertion_stream = get_stream(Key, assertion_stream),
	    put(Key, assertion_stream,
		sicp_streams:cons_stream(Assertion, Current_assertion_stream));
	false -> ok
    end.

store_rule_in_index(Rule) ->
    Pattern = conclusion(Rule),
    case is_indexable(Pattern) of
	true ->
	    Key = index_key_of(Pattern),
	    Current_rule_stream = get_stream(Key, rule_stream),
	    put(Key, rule_stream, 
		sicp_streams:cons_stream(Rule, Current_rule_stream));
	false -> ok
    end.

is_indexable([Car|_]) when is_atom(Car) -> true;
is_indexable(["?"++_|_]) -> true;
is_indexable(_) -> false.

index_key_of(["?"++_|_]) -> '?';
index_key_of([Key|_]) -> Key.

use_index([Car|_]) -> is_atom(Car).

is_rule(Statement) -> is_tagged_list(Statement, 'rule').
































%% ;; Do following to reinit the data base from microshaft-data-base
%% ;;  in Scheme (not in the query driver loop)
%% ;; (initialize-data-base microshaft-data-base)

%% (define microshaft-data-base
%%   '(
%% ;; from section 4.4.1
%% (address (Bitdiddle Ben) (Slumerville (Ridge Road) 10))
%% (job (Bitdiddle Ben) (computer wizard))
%% (salary (Bitdiddle Ben) 60000)

%% (address (Hacker Alyssa P) (Cambridge (Mass Ave) 78))
%% (job (Hacker Alyssa P) (computer programmer))
%% (salary (Hacker Alyssa P) 40000)
%% (supervisor (Hacker Alyssa P) (Bitdiddle Ben))

%% (address (Fect Cy D) (Cambridge (Ames Street) 3))
%% (job (Fect Cy D) (computer programmer))
%% (salary (Fect Cy D) 35000)
%% (supervisor (Fect Cy D) (Bitdiddle Ben))

%% (address (Tweakit Lem E) (Boston (Bay State Road) 22))
%% (job (Tweakit Lem E) (computer technician))
%% (salary (Tweakit Lem E) 25000)
%% (supervisor (Tweakit Lem E) (Bitdiddle Ben))

%% (address (Reasoner Louis) (Slumerville (Pine Tree Road) 80))
%% (job (Reasoner Louis) (computer programmer trainee))
%% (salary (Reasoner Louis) 30000)
%% (supervisor (Reasoner Louis) (Hacker Alyssa P))

%% (supervisor (Bitdiddle Ben) (Warbucks Oliver))

%% (address (Warbucks Oliver) (Swellesley (Top Heap Road)))
%% (job (Warbucks Oliver) (administration big wheel))
%% (salary (Warbucks Oliver) 150000)

%% (address (Scrooge Eben) (Weston (Shady Lane) 10))
%% (job (Scrooge Eben) (accounting chief accountant))
%% (salary (Scrooge Eben) 75000)
%% (supervisor (Scrooge Eben) (Warbucks Oliver))

%% (address (Cratchet Robert) (Allston (N Harvard Street) 16))
%% (job (Cratchet Robert) (accounting scrivener))
%% (salary (Cratchet Robert) 18000)
%% (supervisor (Cratchet Robert) (Scrooge Eben))

%% (address (Aull DeWitt) (Slumerville (Onion Square) 5))
%% (job (Aull DeWitt) (administration secretary))
%% (salary (Aull DeWitt) 25000)
%% (supervisor (Aull DeWitt) (Warbucks Oliver))

%% (can-do-job (computer wizard) (computer programmer))
%% (can-do-job (computer wizard) (computer technician))

%% (can-do-job (computer programmer)
%%             (computer programmer trainee))

%% (can-do-job (administration secretary)
%%             (administration big wheel))

%% (rule (lives-near ?person-1 ?person-2)
%%       (and (address ?person-1 (?town . ?rest-1))
%%            (address ?person-2 (?town . ?rest-2))
%%            (not (same ?person-1 ?person-2))))

%% (rule (same ?x ?x))

%% (rule (wheel ?person)
%%       (and (supervisor ?middle-manager ?person)
%%            (supervisor ?x ?middle-manager)))

%% (rule (outranked-by ?staff-person ?boss)
%%       (or (supervisor ?staff-person ?boss)
%%           (and (supervisor ?staff-person ?middle-manager)
%%                (outranked-by ?middle-manager ?boss))))
%% ))
