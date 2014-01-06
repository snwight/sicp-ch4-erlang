%%
%% WIP - this is a combination of the cutting room floor and the remaining high level logic;
%%       most of this file has been duplicated (and is replaced by) sicp_query_db_server.erl
%%
%% ...snwight jan 6 2014
%%
-module('sicp_query').

-export([query_driver_loop/0]).
-export([]).

%% snwight
%% XXX placeholder
-define(THE_EMPTY_STREAM, []).

%% ;;(put 'always-true 'qeval always-true)

find_assertions(Pattern, Frame) ->
    stream_flatmap(
      fun(Datum) ->
	      check_an_assertion(Datum, Pattern, Frame)
      end, fetch_assertions(Pattern, Frame)).

check_an_assertion(Assertion, Query_pat, Query_frame) ->
    case pattern_match(Query_pat, Assertion, Query_frame) of
	failed -> ?THE_EMPTY_STREAM;
	Match_result -> singleton_stream(Match_result)
    end.

pattern_match(_Pat, _Dat, failed) -> failed;
pattern_match(Pat, Dat, Frame) when Pat =:= Dat -> Frame;
pattern_match(Pat="?"++_, Dat, Frame) -> extend_if_consistent(Pat, Dat, Frame);
pattern_match([CarP|CdrP], [CarD|CdrD], Frame) -> 
    pattern_match(CdrP, CdrD, pattern_match(CarP, CarD, Frame));
pattern_match(_Pat, _Dat, _Frame) -> failed.

extend_if_consistent(Var, Dat, Frame) ->
    case binding_in_frame(Var, Frame) of
	Binding -> pattern_match(binding_value(Binding), Dat, Frame);
	_ -> extend(Var, Dat, Frame)
    end.

%% ;;;SECTION 4.4.4.4
%% ;;;Rules and Unification

%% ;;;SECTION 4.4.4.5
%% ;;;Maintaining the Data Base

%% (define THE-ASSERTIONS the-empty-stream)
-define(THE_ASSERTIONS, ?THE_EMPTY_STREAM).

%% (define (get-all-assertions) THE-ASSERTIONS)
-define(GET_ALL_ASSERTIONS, ?THE_ASSERTIONS).

%% (define (fetch-assertions pattern frame)
%%   (if (use-index? pattern)
%%       (get-indexed-assertions pattern)
%%       (get-all-assertions)))
fetch_assertions(Pattern, _Frame) ->
    case use_index(Pattern) of
	true -> get_indexed_assertions(Pattern);
	false -> ?GET_ALL_ASSERTIONS
    end.

%% (define (get-indexed-assertions pattern)
%%   (get-stream (index-key-of pattern) 'assertion-stream))
get_indexed_assertions(Pattern) ->
    get_stream(index_key_of(Pattern), assertion_stream).

%% (define (get-stream key1 key2)
%%   (let ((s (get key1 key2)))
%%     (if s s the-empty-stream)))
get_stream(Key1, Key2) ->
    case get(Key1, Key2) of
	[] -> ?THE_EMPTY_STREAM;
	S -> S
    end.

%% (define THE-RULES the-empty-stream)
-define(THE_RULES, ?THE_EMPTY_STREAM).

%% (define (get-all-rules) THE-RULES)
get_all_rules() -> ?THE_RULES.

%% (define (fetch-rules pattern frame)
%%   (if (use-index? pattern)
%%       (get-indexed-rules pattern)
%%       (get-all-rules)))
fetch_rules(Pattern, _Frame) ->
   case use_index(Pattern) of
       true -> get_indexed_rules(Pattern);
       false -> get_all_rules()
   end.

%% (define (get-indexed-rules pattern)
%%   (stream-append
%%    (get-stream (index-key-of pattern) 'rule-stream)
%%    (get-stream '? 'rule-stream)))
get_indexed_rules(Pattern) ->
    stream_append(
      get_stream(index_key_of(Pattern), rule_stream),
      get_stream('?', rule_stream)).

%% (define (add-rule-or-assertion! assertion)
%%   (if (rule? assertion)
%%       (add-rule! assertion)
%%       (add-assertion! assertion)))
add_rule_or_assertion(Assertion) ->
   case is_rule(Assertion) of
       true -> add_rule(Assertion);
       false -> add_assertion(Assertion)
   end.

%% (define (add-assertion! assertion)
%%   (store-assertion-in-index assertion)
%%   (let ((old-assertions THE-ASSERTIONS))
%%     (set! THE-ASSERTIONS
%%           (cons-stream assertion old-assertions))
%%     'ok))
add_assertion(Assertion) ->
    store_assertion_in_index(Assertion),
    Old_assertions = ?THE_ASSERTIONS,
    set(?THE_ASSERTIONS, cons_stream(Assertion, Old_assertions)), 
    ok.

%% (define (add-rule! rule)
%%   (store-rule-in-index rule)
%%   (let ((old-rules THE-RULES))
%%     (set! THE-RULES (cons-stream rule old-rules))
%%     'ok))
add_rule(Rule) ->
    store_rule_in_index(Rule),
    Old_rules = ?THE_RULES,
    set(?THE_RULES, cons_stream(Rule, Old_rules)),
    ok.

%% (define (store-assertion-in-index assertion)
%%   (if (indexable? assertion)
%%       (let ((key (index-key-of assertion)))
%%         (let ((current-assertion-stream
%%                (get-stream key 'assertion-stream)))
%%           (put key
%%                'assertion-stream
%%                (cons-stream assertion
%%                             current-assertion-stream))))))
store_assertion_in_index(Assertion) ->
    case is_indexable(Assertion) of
	true ->
	    Key = index_key_of(Assertion),
	    Current_assertion_stream = get_stream(Key, assertion_stream),
	    put(Key, assertion_stream,
		cons_stream(Assertion, Current_assertion_stream))
    end.

%% (define (store-rule-in-index rule)
%%   (let ((pattern (conclusion rule)))
%%     (if (indexable? pattern)
%%         (let ((key (index-key-of pattern)))
%%           (let ((current-rule-stream
%%                  (get-stream key 'rule-stream)))
%%             (put key
%%                  'rule-stream
%%                  (cons-stream rule
%%                               current-rule-stream)))))))
store_rule_in_index(Rule) ->
    Pattern = conclusion(Rule),
    case is_indexable(Pattern) of
	true ->
	    Key = index_key_of(Pattern),
	    Current_rule_stream = get_stream(Key, rule_stream),
	    put(Key, rule_stream, cons_stream(Rule, Current_rule_stream))
    end.

%% (define (indexable? pat)
%%   (or (constant-symbol? (car pat))
%%       (var? (car pat))))
is_indexable([Car|_]) when is_atom(Car) -> true;
is_indexable(["?"++_|_]) -> true;
is_indexable(_) -> false.

%% (define (index-key-of pat)
%%   (let ((key (car pat)))
%%     (if (var? key) '? key)))
index_key_of(["?"++_|_]) -> '?';
index_key_of([Key|_]) -> Key.

%% (define (use-index? pat)
%%   (constant-symbol? (car pat)))
use_index([Car|_]) -> is_atom(Car).

%% ;;;SECTION 4.4.4.6
%% ;;;Stream operations

%% (define (stream-append-delayed s1 delayed-s2)
%%   (if (stream-null? s1)
%%       (force delayed-s2)
%%       (cons-stream
%%        (stream-car s1)
%%        (stream-append-delayed (stream-cdr s1) delayed-s2))))
stream_append_delayed(S1, Delayed_S2) ->
    case is_stream_null(S1) of
	true -> force(Delayed_S2);
	false -> cons_stream(stream_car(S1),
			     stream_append_delayed(
			       stream_cdr(S1), Delayed_S2))
    end.

%% (define (interleave-delayed s1 delayed-s2)
%%   (if (stream-null? s1)
%%       (force delayed-s2)
%%       (cons-stream
%%        (stream-car s1)
%%        (interleave-delayed (force delayed-s2)
%%                            (delay (stream-cdr s1))))))
interleave_delayed(S1, Delayed_S2) ->
    case is_stream_null(S1) of
	true -> force(Delayed_S2);
	false -> cons_stream(stream_car(S1),
			     interleave_delayed(
			       force(Delayed_S2),
			       delay(stream_cdr(S1))))
    end.

%% (define (stream-flatmap proc s)
%%   (flatten-stream (stream-map proc s)))
stream_flatmap(Proc, S) ->
    flatten_stream(stream_map(Proc, S)).

%% (define (flatten-stream stream)
%%   (if (stream-null? stream)
%%       the-empty-stream
%%       (interleave-delayed
%%        (stream-car stream)
%%        (delay (flatten-stream (stream-cdr stream))))))
flatten_stream(Stream) ->
    case is_stream_null(Stream) of
	true -> ?THE_EMPTY_STREAM;
	false -> interleave_delayed(
		   stream_car(Stream),
		   delay(flatten_stream(stream_cdr(Stream))))
    end.

%% (define (singleton-stream x)
%%   (cons-stream x the-empty-stream))
singleton_stream(X) -> cons_stream(X, ?THE_EMPTY_STREAM).

%% ;;;;Stream support from Chapter 3

%% (define (stream-map proc s)
%%   (if (stream-null? s)
%%       the-empty-stream
%%       (cons-stream (proc (stream-car s))
%%                    (stream-map proc (stream-cdr s)))))
stream_map(Proc, S) ->
    case is_stream_null(S) of
	true -> ?THE_EMPTY_STREAM;
	false -> cons_stream(Proc(stream_car(S)), 
			     stream_map(Proc, stream_cdr(S)))
    end.

%% (define (stream-for-each proc s)
%%   (if (stream-null? s)
%%       'done
%%       (begin (proc (stream-car s))
%%              (stream-for-each proc (stream-cdr s)))))
stream_for_each(Proc, S) ->
    case is_stream_null(S) of
	true -> done;
	false ->
	    Proc(stream_car(S)),
	    stream_for_each(Proc, stream_cdr(S))
    end.

%% (define (display-stream s)
%%   (stream-for-each display-line s))
display_stream(S) -> 
    stream_for_each(fun display_line/1, S).

%% (define (display-line x)
%%   (newline)
%%   (display x))
display_line(X) -> 
    io:format("~n~s", [X]).

%% (define (stream-filter pred stream)
%%   (cond ((stream-null? stream) the-empty-stream)
%%         ((pred (stream-car stream))
%%          (cons-stream (stream-car stream)
%%                       (stream-filter pred
%%                                      (stream-cdr stream))))
%%         (else (stream-filter pred (stream-cdr stream)))))
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

%% (define (stream-append s1 s2)
%%   (if (stream-null? s1)
%%       s2
%%       (cons-stream (stream-car s1)
%%                    (stream-append (stream-cdr s1) s2))))
stream_append(S1, S2) ->
    case is_stream_null(S1) of
	true -> S2;
	false -> cons_stream(stream_car(S1), 
			     stream_append(stream_cdr(S1), S2))
    end.

%% (define (interleave s1 s2)
%%   (if (stream-null? s1)
%%       s2
%%       (cons-stream (stream-car s1)
%%                    (interleave s2 (stream-cdr s1)))))
interleave(S1, S2) ->
    case is_stream_null(S1) of
	true -> s2;
	false -> cons_stream(stream_car(S1), 
			     interleave(S2, stream_cdr(S1)))
    end.

%% ;;;;Table support from Chapter 3, Section 3.3.3 (local tables)

%% (define (make-table)
%%   (let ((local-table (list '*table*)))
%%     (define (lookup key-1 key-2)
%%       (let ((subtable (assoc key-1 (cdr local-table))))
%%         (if subtable
%%             (let ((record (assoc key-2 (cdr subtable))))
%%               (if record
%%                   (cdr record)
%%                   false))
%%             false)))
%%     (define (insert! key-1 key-2 value)
%%       (let ((subtable (assoc key-1 (cdr local-table))))
%%         (if subtable
%%             (let ((record (assoc key-2 (cdr subtable))))
%%               (if record
%%                   (set-cdr! record value)
%%                   (set-cdr! subtable
%%                             (cons (cons key-2 value)
%%                                   (cdr subtable)))))
%%             (set-cdr! local-table
%%                       (cons (list key-1
%%                                   (cons key-2 value))
%%                             (cdr local-table)))))
%%       'ok)    
%%     (define (dispatch m)
%%       (cond ((eq? m 'lookup-proc) lookup)
%%             ((eq? m 'insert-proc!) insert!)
%%             (else (error "Unknown operation -- TABLE" m))))
%%     dispatch))
make_table() ->
    Local_table = ['*table*'],
    Lookup = 
	fun(Key_1, Key_2) ->
		[_|CdrLoc] = Local_table,
		Subtable = assoc(Key_1, CdrLoc),
		case Subtable of
		    [] ->  false;
		    _ ->
			[_|CdrSub] = Subtable,
			Record = assoc(Key_2, CdrSub),
			[CdrRec|_] = Record,
			case Record of
			    [] -> false;
			    _ -> CdrRec
			end
		end
	end,
    Insert = 
	fun(Key_1, Key_2, Value) ->
		[_|CdrLoc] = Local_table,
		Subtable = assoc(Key_1, CdrLoc),
		case Subtable of
		    [] -> set_cdr(Local_table, [[Key_1|[Key_2|Value]]|CdrLoc]);
		    _ -> 
			[_|CdrSub] = Subtable,
			Record = assoc(Key_2, CdrSub),
			case Record of
			    [] -> set_cdr(Subtable, [[Key_2 | Value]|CdrSub]);
			    _ -> set_cdr(Record, Value)
			end
		end,
		ok
	end,
    fun('lookup-proc') -> Lookup;
       ('insert-proc') -> Insert;
       (M) -> error("Unknown operation -- TABLE", M)
    end.

%% ;;;; From instructor's manual

%% (define get '())
%% (define put '())

%% (define (initialize-data-base rules-and-assertions)
%%   (define (deal-out r-and-a rules assertions)
%%     (cond ((null? r-and-a)
%%            (set! THE-ASSERTIONS (list->stream assertions))
%%            (set! THE-RULES (list->stream rules))
%%            'done)
%%           (else
%%            (let ((s (query-syntax-process (car r-and-a))))
%%              (cond ((rule? s)
%%                     (store-rule-in-index s)
%%                     (deal-out (cdr r-and-a)
%%                               (cons s rules)
%%                               assertions))
%%                    (else
%%                     (store-assertion-in-index s)
%%                     (deal-out (cdr r-and-a)
%%                               rules
%%                               (cons s assertions))))))))
%%   (let ((operation-table (make-table)))
%%     (set! get (operation-table 'lookup-proc))
%%     (set! put (operation-table 'insert-proc!)))
%%   (put 'and 'qeval conjoin)
%%   (put 'or 'qeval disjoin)
%%   (put 'not 'qeval negate)
%%   (put 'lisp-value 'qeval lisp-value)
%%   (put 'always-true 'qeval always-true)
%%   (deal-out rules-and-assertions '() '()))

get(Key1, Key2) ->
    F = Operation_table('lookup-proc'),
    F(Key1, Key2).
put(Key, S1, S2) -> 
    F = Operation_table('insert-proc'),
    F(Key, S1, S2).

initialize_data_base(Rules_and_assertions) ->
    Operation_table = make_table(),
    Get = Operation_table('lookup-proc'), 
    Put = Operation_table('insert-proc'), 
    Put('and', 'qeval', conjoin),
    Put('or', 'qeval', disjoin),
    Put('not', 'qeval', negate),
    Put('lisp-value', 'qeval', lisp_value),
    Put('always-true', 'qeval', always_true),
    deal_out(Rules_and_assertions, [], []).

deal_out([], Rules, Assertions) ->
    ets:insert(op_tab, {the_assertions, list_to_stream(Assertions)}),
    ets:insert(op_tab, {the_rules, list_to_stream(Rules)}),
    done;
deal_out([Car|Cdr], Rules, Assertions) ->
    S = query_syntax_process(Car),
    case is_rule(S) of
	true ->
	    store_rule_in_index(S),
	    deal_out(Cdr, [S|Rules], Assertions);
	false ->
	    store_assertion_in_index(S),
	    deal_out(Cdr, Rules, [S|Assertions])
    end.

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
