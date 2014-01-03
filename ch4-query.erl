-module('PRE_OTP.sicp_query').

-export([query_driver_loop/0]).
-export([]).

%% snwight
%% XXX placeholder
-define(THE_EMPTY_STREAM, []).

%% handrolled implementation of delay/force - translated from scheme
delay(Exp) -> fun() -> Exp end.
force(Promise) -> Promise.

%% STREAMS from ch3
%% (cons-stream <a> <b>) ====> (cons <a> (delay <b>))
cons_stream(Car, Cdr) -> [Car|delay(Cdr)].
 
%% (define (stream-car stream) (car stream))
%% (define (stream-cdr stream) (force (cdr stream)))
stream_car([Car|_]) -> Car.
stream_cdr([_|Cdr]) -> force(Cdr).

list_to_stream(List) -> List.

%% (define (memo-proc proc)
%%   (let ((already-run? false) (result false))
%%     (lambda ()
%%       (if (not already-run?)
%%           (begin (set! result (proc))
%%                  (set! already-run? true)
%%                  result)
%%           result))))
%% eg: (memo-proc (lambda () <exp>))

%% ;;;;QUERY SYSTEM FROM SECTION 4.4.4 OF
%% ;;;; STRUCTURE AND INTERPRETATION OF COMPUTER PROGRAMS

%% ;;;SECTION 4.4.4.1
%% ;;;The Driver Loop and Instantiation

%% (define input-prompt ";;; Query input:")
%% (define output-prompt ";;; Query results:")
-define(INPUT_PROMPT, ";;; Query input:").
-define(OUTPUT_PROMPT, ";;; Query results:").

%% (define (query-driver-loop)
%%   (prompt-for-input input-prompt)
%%   (let ((q (query-syntax-process (read))))
%%     (cond ((assertion-to-be-added? q)
%%            (add-rule-or-assertion! (add-assertion-body q))
%%            (newline)
%%            (display "Assertion added to data base.")
%%            (query-driver-loop))
%%           (else
%%            (newline)
%%            (display output-prompt)
%%            ;; [extra newline at end] (announce-output output-prompt)
%%            (display-stream
%%             (stream-map
%%              (lambda (frame)
%%                (instantiate q
%%                             frame
%%                             (lambda (v f)
%%                               (contract-question-mark v))))
%%              (qeval q (singleton-stream '()))))
%%            (query-driver-loop)))))
query_driver_loop() ->
    io:format("~n~s", [?INPUT_PROMPT]),
    Q = query_syntax_process(read),
    case assertion_to_be_added(Q) of
	true ->
	    add_rule_or_assertion(add_assertion_body(Q)),
	    io:format("~nAssertion added to data base.", []),
	    query_driver_loop();
	false ->
	    io:format("~n~s", [?OUTPUT_PROMPT]),
	    %%	    announce_output(?OUTPUT_PROMPT),
	    display_stream(
	      stream_map(
		fun(Frame) ->
			instantiate(Q, Frame,
				    fun(V, F) ->
					    contract_question_mark(V)
				    end)
		end,
		qeval(Q, singleton_stream([])))),
	    query_driver_loop()
    end.

%% (define (instantiate exp frame unbound-var-handler)
%%   (define (copy exp)
%%     (cond ((var? exp)
%%            (let ((binding (binding-in-frame exp frame)))
%%              (if binding
%%                  (copy (binding-value binding))
%%                  (unbound-var-handler exp frame))))
%%           ((pair? exp)
%%            (cons (copy (car exp)) (copy (cdr exp))))
%%           (else exp)))
%%   (copy exp))
instantiate(Exp="?" ++ _, Frame, Unbound_var_handler) ->
    case binding_in_frame(Exp, Frame) of
	[] -> Unbound_var_handler(Exp, Frame);
	Binding -> instantiate(binding_value(Binding), 
			       Frame, Unbound_var_handler)
    end;
instantiate([Car|Cdr], Frame, Unbound_var_handler) ->
    [instantiate(Car, Frame, Unbound_var_handler) | 
     instantiate(Cdr, Frame, Unbound_var_handler)];
instantiate(Exp, _Frame, _Unbound_var_handler) -> 
    Exp.

%% ;;;SECTION 4.4.4.2
%% ;;;The Evaluator

%% (define (qeval query frame-stream)
%%   (let ((qproc (get (type query) 'qeval)))
%%     (if qproc
%%         (qproc (contents query) frame-stream)
%%         (simple-query query frame-stream))))
qeval(Query, Frame_stream) ->
    case get(type(Query), qeval) of
	[] -> simple_query(Query, Frame_stream);
	Qproc -> Qproc(contents(Query), Frame_stream)
    end.

%% ;;;Simple queries

%% (define (simple-query query-pattern frame-stream)
%%   (stream-flatmap
%%    (lambda (frame)
%%      (stream-append-delayed
%%       (find-assertions query-pattern frame)
%%       (delay (apply-rules query-pattern frame))))
%%    frame-stream))
simple_query(Query_pattern, Frame_stream) ->
    stream_flatmap(
      fun(Frame) -> 
	      stream_append_delayed(
		find_assertions(Query_pattern, Frame),
		delay(apply_rules(Query_pattern, Frame)))
      end, Frame_stream).

%% ;;;Compound queries

%% (define (conjoin conjuncts frame-stream)
%%   (if (empty-conjunction? conjuncts)
%%       frame-stream
%%       (conjoin (rest-conjuncts conjuncts)
%%                (qeval (first-conjunct conjuncts)
%%                       frame-stream))))
conjoin(Conjuncts, Frame_stream) ->
    case empty_conjunction(Conjuncts) of
	true -> Frame_stream;
	false -> conjoin(rest_conjuncts(Conjuncts),
			 qeval(first_conjunct(Conjuncts),
			       Frame_stream))
    end.

%% ;;(put 'and 'qeval conjoin)

%% (define (disjoin disjuncts frame-stream)
%%   (if (empty-disjunction? disjuncts)
%%       the-empty-stream
%%       (interleave-delayed
%%        (qeval (first-disjunct disjuncts) frame-stream)
%%        (delay (disjoin (rest-disjuncts disjuncts)
%%                        frame-stream)))))
disjoin(Disjuncts, Frame_stream) ->
    case empty_disjunction(Disjuncts) of
	false -> interleave_delayed(
		   qeval(first_disjunct(Disjuncts), Frame_stream),
		   delay(disjoin(rest_disjuncts(Disjuncts), Frame_stream)));
	true -> ?THE_EMPTY_STREAM
    end.
	      
%% ;;(put 'or 'qeval disjoin)

%% ;;;Filters

%% snwight
is_stream_null([]) -> true;
is_stream_null(_) -> false.
    
%% (define (negate operands frame-stream)
%%   (stream-flatmap
%%    (lambda (frame)
%%      (if (stream-null? (qeval (negated-query operands)
%%                               (singleton-stream frame)))
%%          (singleton-stream frame)
%%          the-empty-stream))
%%    frame-stream))
negate(Operands, Frame_stream) ->
    stream_flatmap(
      fun(Frame) ->
	      S = qeval(negated_query(Operands), singleton_stream(Frame)),
	      case is_stream_null(S) of
		  true -> singleton_stream(Frame);
		  false -> ?THE_EMPTY_STREAM
	      end
      end,
      Frame_stream).

%% ;;(put 'not 'qeval negate)

%% (define (lisp-value call frame-stream)
%%   (stream-flatmap
%%    (lambda (frame)
%%      (if (execute
%%           (instantiate
%%            call
%%            frame
%%            (lambda (v f)
%%              (error "Unknown pat var -- LISP-VALUE" v))))
%%          (singleton-stream frame)
%%          the-empty-stream))
%%    frame-stream))
lisp_value(Call, Frame_stream) ->
    stream_flatmap(
      fun(Frame) ->
	      Res = execute(
		      instantiate(
			Call, Frame,
			fun(V, F) ->
				error("Unknown pat var -- LISP-VALUE", V)
			end)),
	      case Res of
		  true -> singleton_stream(Frame);
		  false -> ?THE_EMPTY_STREAM
	      end
      end, Frame_stream).

%% ;;(put 'lisp-value 'qeval lisp-value)

%% (define (execute exp)
%%   (apply (eval (predicate exp) user-initial-environment)
%%          (args exp)))
execute(_Exp) ->
    %% snwight
    %% XXX whoopsie ???
    %%    apply(eval(Predicate(Exp), User_initial_environment), Args, Exp).
    [].

%% (define (always-true ignore frame-stream) frame-stream)
always_true(_Ignore, Frame_stream) -> Frame_stream.

%% ;;(put 'always-true 'qeval always-true)

%% ;;;SECTION 4.4.4.3
%% ;;;Finding Assertions by Pattern Matching

%% (define (find-assertions pattern frame)
%%   (stream-flatmap (lambda (datum)
%%                     (check-an-assertion datum pattern frame))
%%                   (fetch-assertions pattern frame)))
find_assertions(Pattern, Frame) ->
    stream_flatmap(
      fun(Datum) ->
	      check_an_assertion(Datum, Pattern, Frame)
      end, fetch_assertions(Pattern, Frame)).

%% (define (check-an-assertion assertion query-pat query-frame)
%%   (let ((match-result
%%          (pattern-match query-pat assertion query-frame)))
%%     (if (eq? match-result 'failed)
%%         the-empty-stream
%%         (singleton-stream match-result))))
check_an_assertion(Assertion, Query_pat, Query_frame) ->
    case pattern_match(Query_pat, Assertion, Query_frame) of
	failed -> ?THE_EMPTY_STREAM;
	Match_result -> singleton_stream(Match_result)
    end.

%% (define (pattern-match pat dat frame)
%%   (cond ((eq? frame 'failed) 'failed)
%%         ((equal? pat dat) frame)
%%         ((var? pat) (extend-if-consistent pat dat frame))
%%         ((and (pair? pat) (pair? dat))
%%          (pattern-match (cdr pat)
%%                         (cdr dat)
%%                         (pattern-match (car pat)
%%                                        (car dat)
%%                                        frame)))
%%         (else 'failed)))
pattern_match(_Pat, _Dat, failed) -> failed;
pattern_match(Pat, Dat, Frame) when Pat =:= Dat -> Frame;
pattern_match(Pat="?"++_, Dat, Frame) -> extend_if_consistent(Pat, Dat, Frame);
pattern_match([CarP|CdrP], [CarD|CdrD], Frame) -> 
    pattern_match(CdrP, CdrD, pattern_match(CarP, CarD, Frame));
pattern_match(_Pat, _Dat, _Frame) -> failed.

%% (define (extend-if-consistent var dat frame)
%%   (let ((binding (binding-in-frame var frame)))
%%     (if binding
%%         (pattern-match (binding-value binding) dat frame)
%%         (extend var dat frame))))
extend_if_consistent(Var, Dat, Frame) ->
    case binding_in_frame(Var, Frame) of
	Binding -> pattern_match(binding_value(Binding), Dat, Frame);
	_ -> extend(Var, Dat, Frame)
    end.

%% ;;;SECTION 4.4.4.4
%% ;;;Rules and Unification

%% (define (apply-rules pattern frame)
%%   (stream-flatmap (lambda (rule)
%%                     (apply-a-rule rule pattern frame))
%%                   (fetch-rules pattern frame)))
apply_rules(Pattern, Frame) ->
    stream_flatmap(
      fun(Rule) ->
	      apply_a_rule(Rule, Pattern, Frame)
      end, fetch_rules(Pattern, Frame)).

%% (define (apply-a-rule rule query-pattern query-frame)
%%   (let ((clean-rule (rename-variables-in rule)))
%%     (let ((unify-result
%%            (unify-match query-pattern
%%                         (conclusion clean-rule)
%%                         query-frame)))
%%       (if (eq? unify-result 'failed)
%%           the-empty-stream
%%           (qeval (rule-body clean-rule)
%%                  (singleton-stream unify-result))))))
apply_a_rule(Rule, Query_pattern, Query_frame) ->
    Clean_rule = rename_variables_in(Rule),
    case unify_match(Query_pattern, conclusion(Clean_rule), Query_frame) of
	failed -> ?THE_EMPTY_STREAM;
	Unify_result -> qeval(rule_body(Clean_rule), 
			      singleton_stream(Unify_result))
    end.

%% (define (rename-variables-in rule)
%%   (let ((rule-application-id (new-rule-application-id)))
%%     (define (tree-walk exp)
%%       (cond ((var? exp)
%%              (make-new-variable exp rule-application-id))
%%             ((pair? exp)
%%              (cons (tree-walk (car exp))
%%                    (tree-walk (cdr exp))))
%%             (else exp)))
%%     (tree-walk rule)))
rename_variables_in(Rule) -> tree_walk(Rule, new_rule_application_id()).

%% snwight
tree_walk(Rule="?"++_, Id) -> make_new_variable(Rule, Id);
tree_walk([Car|Cdr], Id)   -> [tree_walk(Car, Id) | tree_walk(Cdr, Id)];
tree_walk(Rule, _Id)       -> Rule.

%% (define (unify-match p1 p2 frame)
%%   (cond ((eq? frame 'failed) 'failed)
%%         ((equal? p1 p2) frame)
%%         ((var? p1) (extend-if-possible p1 p2 frame))
%%         ((var? p2) (extend-if-possible p2 p1 frame)) ; {\em ; ***}
%%         ((and (pair? p1) (pair? p2))
%%          (unify-match (cdr p1)
%%                       (cdr p2)
%%                       (unify-match (car p1)
%%                                    (car p2)
%%                                    frame)))
%%         (else 'failed)))
unify_match(_P1, _P2, failed)                    -> failed;
unify_match(P1, P2, Frame) when P1 =:= P2        -> Frame;
unify_match(P1="?"++_, P2, Frame)                -> extend_if_possible(P1, P2, Frame);
unify_match(P1, P2="?"++_, Frame)                -> extend_if_possible(P2, P1, Frame);
unify_match([CarP1|CdrP1], [CarP2|CdrP2], Frame) -> 
    unify_match(CdrP1, CdrP2, unify_match(CarP1, CarP2, Frame));
unify_match(_P1, _P2, _Frame)                    -> failed.

%% (define (extend-if-possible var val frame)
%%   (let ((binding (binding-in-frame var frame)))
%%     (cond (binding
%%            (unify-match
%%             (binding-value binding) val frame))
%%           ((var? val)                     ; {\em ; ***}
%%            (let ((binding (binding-in-frame val frame)))
%%              (if binding
%%                  (unify-match
%%                   var (binding-value binding) frame)
%%                  (extend var val frame))))
%%           ((depends-on? val var frame)    ; {\em ; ***}
%%            'failed)
%%           (else (extend var val frame)))))
extend_if_possible(Var, Val, Frame) ->
   case binding_in_frame(Var, Frame) of
       Binding1 -> unify_match(binding_value(Binding1), Val, Frame);
       _ -> 
	   case Val of
	       "?"++_ -> 
		   case binding_in_frame(Val, Frame) of
		       Binding2 -> unify_match(Var, binding_value(Binding2), Frame);
		       _ -> extend(Var, Val, Frame)
		   end;
	       _ ->
		   case depends_on(Val, Var, Frame) of
		       true -> failed;
		       _ -> extend(Var, Val, Frame)
		   end
	   end
   end.

%% (define (depends-on? exp var frame)
%%   (define (tree-walk e)
%%     (cond ((var? e)
%%            (if (equal? var e)
%%                true
%%                (let ((b (binding-in-frame e frame)))
%%                  (if b
%%                      (tree-walk (binding-value b))
%%                      false))))
%%           ((pair? e)
%%            (or (tree-walk (car e))
%%                (tree-walk (cdr e))))
%%           (else false)))
%%   (tree-walk exp))
depends_on(Exp="?"++_, Var, _Frame) when Exp =:= Var -> true;
depends_on(Exp="?"++_, Var, Frame) -> 
    case binding_in_frame(Exp, Frame) of
	Binding -> depends_on(binding_value(Binding), Var, Frame);
	_ -> false
    end;
depends_on([Car|Cdr], Var, Frame) -> 
    depends_on(Car, Var, Frame) or depends_on(Cdr, Var, Frame);
depends_on(_, _, _) -> false.

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
		cons_stream(Assertion, Current_assertion_stream));
	false -> ok
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
	    put(Key, rule_stream, 
		cons_stream(Rule, Current_rule_stream));
	false -> ok
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

%% ;;;SECTION 4.4.4.7
%% ;;;Query syntax procedures

%% (define (type exp)
%%   (if (pair? exp)
%%       (car exp)
%%       (error "Unknown expression TYPE" exp)))
type([H|_]) -> H;
type(Exp) -> error("Unknown expression TYPE", Exp).

%% (define (contents exp)
%%   (if (pair? exp)
%%       (cdr exp)
%%       (error "Unknown expression CONTENTS" exp)))
contents([_|T]) -> T;
contents(Exp) -> error("Unknown expression CONTENTS", Exp).

%% (define (assertion-to-be-added? exp)
%%   (eq? (type exp) 'assert!))
assertion_to_be_added(Exp) -> type(Exp) == assert.

%% (define (add-assertion-body exp)
%%   (car (contents exp)))
add_assertion_body(Exp) -> lists:nth(1, contents(Exp)).

%% (define (empty-conjunction? exps) (null? exps))
%% (define (first-conjunct exps) (car exps))
%% (define (rest-conjuncts exps) (cdr exps))
empty_conjunction([])   -> true;
empty_conjunction(_)    -> false.
first_conjunct([Car|_]) -> Car.
rest_conjuncts([_|Cdr]) -> Cdr.

%% (define (empty-disjunction? exps) (null? exps))
%% (define (first-disjunct exps) (car exps))
%% (define (rest-disjuncts exps) (cdr exps))
empty_disjunction([])   -> true;
empty_disjunction(_)    -> false.
first_disjunct([Car|_]) -> Car.
rest_disjuncts([_|Cdr]) -> Cdr.

%% (define (negated-query exps) (car exps))
negated_query([Car|_])  -> Car.

%% (define (predicate exps) (car exps))
%% (define (args exps) (cdr exps))
predicate([Car|_])      -> Car.
args([_|Cdr])           -> Cdr.

%% (define (rule? statement)
%%   (tagged-list? statement 'rule))
is_rule(Statement) -> is_tagged_list(Statement, rule).

%% (define (conclusion rule) (cadr rule))
conclusion([_|[H|_]]) -> H.

%% (define (rule-body rule)
%%   (if (null? (cddr rule))
%%       '(always-true)
%%       (caddr rule)))
rule_body([_|[_|[]]]) -> always_true;
rule_body([_|[_|[H|_]]]) -> H.

%% (define (query-syntax-process exp)
%%   (map-over-symbols expand-question-mark exp))
query_syntax_process(Exp) ->
    map_over_symbols(fun expand_question_mark/1, Exp).

%% (define (map-over-symbols proc exp)
%%   (cond ((pair? exp)
%%          (cons (map-over-symbols proc (car exp))
%%                (map-over-symbols proc (cdr exp))))
%%         ((symbol? exp) (proc exp))
%%         (else exp)))
map_over_symbols(Proc, [Car|Cdr]) ->
    [map_over_symbols(Proc, Car) | map_over_symbols(Proc, Cdr)];
map_over_symbols(Proc, Exp) when is_atom(Exp) -> Proc(Exp);
map_over_symbols(_Proc, Exp) -> Exp.

%% (define (expand-question-mark symbol)
%%   (let ((chars (symbol->string symbol)))
%%     (if (string=? (substring chars 0 1) "?")
%%         (list '?
%%               (string->symbol
%%                (substring chars 1 (string-length chars))))
%%         symbol)))
expand_question_mark(Symbol) ->
    Chars = atom_to_list(Symbol),
    case Chars of
	"?"++_ -> ['?'| list_to_atom(lists:nthtail(1, Chars))];
	_ -> Symbol
    end.

%% (define (var? exp)
%%   (tagged-list? exp '?))
is_var(Exp) -> is_tagged_list(Exp, '?').

%% (define (constant-symbol? exp) (symbol? exp))
is_constant_symbol(Exp) -> is_atom(Exp).

%% (define rule-counter 0)

%% (define (new-rule-application-id)
%%   (set! rule-counter (+ 1 rule-counter))
%%   rule-counter)
new_rule_application_id() -> 
    case ets:info(r_and_a_tab) of
	undefined ->
	    Tab = ets:new(r_and_a_tab, [set, named_table, protected]),
	    ets:insert(Tab, {rule_id, 1}),
	    1;
	 _ -> ets:update_counter(r_and_a_tab, rule_id, 1)
    end.

%% (define (make-new-variable var rule-application-id)
%%   (cons '? (cons rule-application-id (cdr var))))
make_new_variable([_|T], Rule_Application_Id) -> 
    ['?'|[Rule_Application_Id|T]].

%% (define (contract-question-mark variable)
%%   (string->symbol
%%    (string-append "?" 
%%      (if (number? (cadr variable))
%%          (string-append (symbol->string (caddr variable))
%%                         "-"
%%                         (number->string (cadr variable)))
%%          (symbol->string (cadr variable))))))
contract_question_mark([_|[Cadr|[Caddr|_]]]) -> 
    V = case is_number(Cadr) of
	    true -> string:concat(atom_to_list(Caddr), "-", 
				  integer_to_list(Cadr));
	    false -> atom_to_list(Cadr)
	end,
    list_to_atom(string:concat("?", V)).

%% ;;;SECTION 4.4.4.8
%% ;;;Frames and bindings
%% (define (make-binding variable value)
%%   (cons variable value))
make_binding(Variable, Value) -> [Variable|Value].

%% (define (binding-variable binding)
%%   (car binding))
binding_variable([Car|_]) -> Car.

%% (define (binding-value binding)
%%   (cdr binding))
binding_value([_|Cdr]) -> Cdr.

%% (define (binding-in-frame variable frame)
%%   (assoc variable frame))
binding_in_frame(Variable, Frame) ->
    %% XXX assuming Frame is tuple list
    lists:keymember(Variable, 1, Frame).

%% (define (extend variable value frame)
%%   (cons (make-binding variable value) frame))
extend(Variable, Value, Frame) -> 
    [make_binding(Variable, Value)|Frame].

%% ;;;;From Section 4.1

%% (define (tagged-list? exp tag)
%%   (if (pair? exp)
%%       (eq? (car exp) tag)
%%       false))
is_tagged_list([Car|_], Tag) when Car == Tag -> true;
is_tagged_list(_, _) -> false.

%% (define (prompt-for-input string)
%%   (newline) (newline) (display string) (newline))
prompt_for_input(String) -> 
    io:format("~n~n~s~n", [String]).

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
    ets:insert(r_and_a_tab, {the_assertions, list_to_stream(Assertions)}),
    ets:insert(r_and_a_tab, {the_rules, list_to_stream(Rules)}),
    done;
deal_out([Car|Cdr], Rules, Assertions) ->
    S = query_syntax_process(Car),
    case is_rule(S) of
	true ->
	    store_rule_in_index(S),
	    deal_out(Cdr, [S|Rules], Assertions);
	_ ->
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
