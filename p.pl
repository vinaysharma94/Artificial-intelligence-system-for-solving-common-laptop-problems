%%%%%%%%%% Rule Based Expert System Shell %%%%%%%%%%
%%%
%%% This is the expert system with the example from the textbook:
%%%
%%% Artificial Intelligence: 
%%% Structures and strategies for complex problem solving
%%%
%%% by George F. Luger and William A. Stubblefield
%%% 
%%% These programs are copyrighted by Benjamin//Cummings Publishers.
%%%
%%% Modified by Shaun-inn Wu
%%%
%%% These program are offered for educational purposes only.
%%%
%%% Disclaimer: These programs are provided with no warranty whatsoever as to
%%% their correctness, reliability, or any other property.  We have written 
%%% them for specific educational purposes, and have made no effort
%%% to produce commercial quality computer programs.  Please do not expect 
%%% more of them then we have intended.
%%%
%%% This code has been tested with SWI-Prolog (Multi-threaded, Version 7.6.4)
%%% and appears to function as intended.


% solve(Goal): solve(fix_car(Advice)) for the car problem.
% Top level call.  Initializes working memory; attempts to solve Goal
% with certainty factor; prints results; asks user if they would like a
% trace.

solve(Goal) :- 
    init, print_help,
    solve(Goal,C,[],1),
    nl,write('Solved '),write(Goal),
    write(' With Certainty = '),write(C),nl,nl,
    ask_for_trace(Goal).

% init
% purges all facts from working memory.

init :- retractm(fact(X)), retractm(untrue(X)).

% solve(Goal,CF,Rulestack,Cutoff_context)
% Attempts to solve Goal by backwards chaining on rules;  CF is
% certainty factor of final conclusion; Rulestack is stack of
% rules, used in why queries, Cutoff_context is either 1 or -1
% depending on whether goal is to be proved true or false
% (e.g. not Goal requires Goal be false in oreder to succeed).

solve(true,100,Rules,_).

solve(A,100,Rules,_) :- 
    fact(A).

solve(A,-100,Rules,_) :-
    untrue(A).

solve(not(A),C,Rules,T) :- 
    T2 is -1 * T,
    solve(A,C1,Rules,T2),
    C is -1 * C1.

solve((A,B),C,Rules,T) :- 
    solve(A,C1,Rules,T), 
    above_threshold(C1,T),
    solve(B,C2,Rules,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

solve(A,C,Rules,T) :- 
    rule((A :- B),C1), 
    solve(B,C2,[rule(A,B,C1)|Rules],T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    rule((A), C),
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    askable(A), 
    not(known(A)), 
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% respond( Answer, Query, CF, Rule_stack).
% respond will process Answer (yes, no, how, why, help).
% asserting to working memory (yes or no)
% displaying current rule from rulestack (why)
% showing proof trace of a goal (how(Goal)
% displaying help (help).
% Invalid responses are detected and the query is repeated.

respond(Bad_answer,A,C,Rules) :- 
    not(member(Bad_answer,[help, yes,no,why,how(_)])),
    write('answer must be either help, (y)es, (n)o, (h)ow(X), (w)hy'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(yes,A,100,_) :- 
    assert(fact(A)).

respond(no,A,-100,_) :- 
    assert(untrue(A)).

respond(why,A,C,[Rule|Rules]) :- 
    display_rule(Rule),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(why,A,C,[]) :-
    write('Back to goal, no more explanation  possible'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,[]).

respond(how(Goal),A,C,Rules) :- 
    respond_how(Goal),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(help,A,C,Rules) :- 
    print_help,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% ask(Query, Answer)
% Writes Query and reads the Answer.  Abbreviations (y, n, h, w) are
% trnslated to appropriate command be filter_abbreviations

ask(Query,Answer) :- 
    display_query(Query),
    read(A),
    filter_abbreviations(A,Answer),!.

% filter_abbreviations( Answer, Command)
% filter_abbreviations will expand Answer into Command.  If
% Answer is not a known abbreviation, then Command = Answer.

filter_abbreviations(y,yes).
filter_abbreviations(n,no).
filter_abbreviations(w,why).
filter_abbreviations(h,help).
filter_abbreviations(h(X),how(X)).
filter_abbreviations(X,X).

% known(Goal)
% Succeeds if Goal is known to be either true or untrue.

known(Goal) :- fact(Goal).
known(Goal) :- untrue(Goal).

% ask_for_trace(Goal).
% Invoked at the end of a consultation, ask_for_trace asks the user if
% they would like a trace of the reasoning to a goal.

ask_for_trace(Goal) :-
    write('Trace of reasoning to goal ? '),
    read(Answer),nl,
    show_trace(Answer,Goal),!.

% show_trace(Answer,Goal)
% If Answer is ``yes'' or ``y,'' show trace will display  a trace
% of Goal, as in a ``how'' query.  Otherwise, it succeeds, doing nothing.

show_trace(yes,Goal) :- respond_how(Goal).

show_trace(y,Goal) :- respond_how(Goal).

show_trace(_,_).

% print_help
% Prints a help screen.

print_help :- 
    write('Exshell allows the following responses to queries:'),nl,nl,
    write('   yes - query is known to be true.'),nl,
    write('   no - query is false.'),nl,
    write('   why - displays rule currently under consideration.'),nl,
    write('   how(X) - if X has been inferred, displays trace of reasoning.'),nl,
    write('   help - prints this message.'),nl,
    write('   Your response may be abbreviated to the first letter and must end with a period (.).'),nl.

% display_query(Goal)
% Shows Goal to user in the form of a query.

display_query(Goal) :-
    write(Goal),
    write('? ').

% display_rule(rule(Head, Premise, CF))
% prints rule in IF...THEN form.

display_rule(rule(Head,Premise,CF)) :-
    write('IF       '),
    write_conjunction(Premise),
    write('THEN     '),
    write(Head),nl,
    write('CF   '),write(CF),
    nl,nl.

% write_conjunction(A)
% write_conjunction will print the components of a rule premise.  If any
% are known to be true, they are so marked.

write_conjunction((A,B)) :-
    write(A), flag_if_known(A),!, nl,
    write('     AND '),
    write_conjunction(B).

write_conjunction(A) :- write(A),flag_if_known(A),!, nl.

% flag_if_known(Goal).
% Called by write_conjunction, if Goal follows from current state
% of working memory, prints an indication, with CF.

flag_if_known(Goal) :- 
    build_proof(Goal,C,_,1), 
    write('     ***Known, Certainty = '),write(C).

flag_if_known(A). 

% Predicates concerned with how queries.

% respond_how(Goal).
% calls build_proof to determine if goal follows from current state of working
% memory.  If it does, prints a trace of reasoning, if not, so indicates.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,-1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    write('Goal does not follow at this stage of consultation.'),nl.

% build_proof(Goal, CF, Proof, Cutoff_context).
% Attempts to prove Goal, placing a trace of the proof in Proof.
% Functins the same as solve, except it does not ask for unknown information.
% Thus, it only proves goals that follow from the rule base and the current 
% contents of working memory.

build_proof(true,100,(true,100),_).

build_proof(Goal, 100, (Goal :- given,100),_) :- fact(Goal).

build_proof(Goal, -100, (Goal :- given,-100),_) :- untrue(Goal).

build_proof(not(Goal), C, (not(Proof),C),T) :- 
    T2 is -1 * T,
    build_proof(Goal,C1,Proof,T2),
    C is -1 * C1.

build_proof((A,B),C,(ProofA, ProofB),T) :-
    build_proof(A,C1,ProofA,T),
    above_threshold(C1,T),
    build_proof(B,C2,ProofB,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

build_proof(A, C, (A :- Proof,C),T) :-
    rule((A :- B),C1), 
    build_proof(B, C2, Proof,T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

build_proof(A, C, (A :- true,C),T) :-
    rule((A),C),
    above_threshold(C,T).

% interpret(Proof).
% Interprets a Proof as constructed by build_proof,
% printing a trace for the user.

interpret((Proof1,Proof2)) :-
    interpret(Proof1),interpret(Proof2).

interpret((Goal :- given,C)):-
    write(Goal),
    write(' was given. CF = '), write(C),nl,nl.

interpret((not(Proof), C)) :-
    extract_body(Proof,Goal),
    write('not '),
    write(Goal),
    write(' CF = '), write(C),nl,nl,
    interpret(Proof).

interpret((Goal :- true,C)) :-
    write(Goal),
        write(' is a fact, CF = '),write(C),nl.

interpret(Proof) :-
    is_rule(Proof,Head,Body,Proof1,C),
    nl,write(Head),write(' CF = '),
    write(C), nl,write('was proved using the rule'),nl,nl,
    rule((Head :- Body),CF),
    display_rule(rule(Head, Body,CF)), nl,
    interpret(Proof1).

% isrule(Proof,Goal,Body,Proof,CF)
% If Proof is of the form Goal :- Proof, extracts
% rule Body from Proof.

is_rule((Goal :- Proof,C),Goal, Body, Proof,C) :-
    not(member(Proof, [true,given])),
    extract_body(Proof,Body).

% extract_body(Proof).
% extracts the body of the top level rule from Proof.

extract_body((not(Proof), C), (not(Body))) :-
    extract_body(Proof,Body).

extract_body((Proof1,Proof2),(Body1,Body2)) :-
    !,extract_body(Proof1,Body1),
    extract_body(Proof2,Body2).

extract_body((Goal :- Proof,C),Goal).
    
% Utility Predicates.

retractm(X) :- retract(X), fail.
retractm(X) :- retract((X:-Y)), fail.
retractm(X).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

minimum(X,Y,X) :- X =< Y.
minimum(X,Y,Y) :- Y < X.

above_threshold(X,1) :- X >= 20.
above_threshold(X,-1) :- X =< -20.





% Top level goal, starts search.
rule((customer_care(Issue):- problem(Y), fix(Y,Issue)),100).


%% Rules for valid inputs to system: 
rule((customer_care(overheating) :- problem(overheating)),60). 
rule((customer_care(need_more_memory) :- problem(need_more_memory)),85). 
rule((customer_care(slow_hard_drive) :- problem(slow_hard_drive)),75). 
rule((customer_care(replace_battery) :- problem(replace_battery)),80). 
rule((customer_care(remove_battery) :- problem(remove_battery)),85). 
rule((customer_care(antivirus_not_installed) :- problem(antivirus_not_installed)),90). 
rule((customer_care(antivirus_not_updated) :- problem(antivirus_not_updated)),87). 
rule((customer_care(invalid_input) :- problem(invalid_input)),65). 





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Rules for knowledge base of system.

rule((problem(overheating):- (system_crashing),(system_freezing),(frequent_shut_down),(fan_working_properly)),60).
rule((problem(need_more_memory):- (overheating),(low_performance_when_using_multiple_applications),(hangups),(excessive_bootup_time),not(fan_working_properly),(fan_making_more_noise)),85).
rule((problem(need_more_memory):- (overheating),(low_performance_when_using_multiple_applications),(hangups),(excessive_bootup_time),(fan_working_properly),(fan_making_more_noise)),75).
rule((problem(slow_hard_drive):- (program_takes_long_time_to_load),(slow_file_transfer)),75).
rule((problem(replace_battery):- (laptop_works_only_for_few_hours_after_charging),(battery_drains_when_using_multiple_application)),80).
rule((problem(remove_battery):- (power_button_has_light),not(keyboard_lights_on),(black_screen),(battery_charged),not(fan_working)),85).
rule((problem(antivirus_not_installed):- (excessive_popups),(system_freezing),(slow_downloads),not(anitivirus_installed),(sluggish_performance)),90).
rule((problem(antivirus_not_updated):- (excessive_popups),(system_freezing),(slow_downloads),(anitivirus_installed)),87).
rule((problem(replace_battery):- (system_crashing),(system_freezing),not(frequent_shut_down),not(overheating),(program_takes_long_time_to_load),not(slow_file_transfer),(laptop_works_only_for_few_hours_after_charging),(battery_drains_when_using_multiple_application)),50).
rule((problem(invalid_input):- not(system_crashing),not(overheating),not(program_takes_long_time_to_load),not(laptop_works_only_for_few_hours_after_charging),not(power_button_has_light),not(excessive_popups)),65).

% Rules to provide solution to the issue.

rule(fix(overheating, 'Problem is overheating. Please clean air vent or put filtered material over inhalation vein or update BIOS '),100).
rule(fix(need_more_memory, 'Problem is need for memory. Please update the RAM '),100).
rule(fix(slow_hard_drive, 'Problem is slow hard drive. Please use inbuilt tool disk defragmenter to defragment disk. '),100).
rule(fix(replace_battery, 'Problem is battery. Please replace the battery '),100).
rule(fix(remove_battery, 'Problem is battery. Please remove battery from slot.Insert battey again and try to start the system. If this does not work replace the battery '),100).
rule(fix(antivirus_not_installed, 'Problem is antivirus not installed. Please install a antivirus. '),100).
rule(fix(antivirus_not_updated, 'Problem is antivirus not updated. Please update the antivirus.'),100).
rule(fix(invalid_input, 'System cannot process with these inputs.Please try again with valid inputs.'),100).

%askable(overheating).
askable(system_crashing).
askable(system_freezing).
askable(frequent_shut_down).
askable(fan_working_properly).
%askable(need_more_memory).
askable(overheating).
askable(low_performance_when_using_multiple_applications).
askable(hangups).
askable(excessive_bootup_time).
askable(fan_working_properly).
askable(fan_making_more_noise).
%askable(slow_hard_drive).
askable(program_takes_long_time_to_load).
askable(slow_file_transfer).
%askable(replace_battery).
askable(laptop_works_only_for_few_hours_after_charging).
askable(battery_drains_when_using_multiple_application).
%askable(remove_battery).
askable(power_button_has_light).
askable(keyboard_lights_on).
askable(black_screen).
askable(battery_charged).
askable(fan_working).
%askable(antivirus).
askable(excessive_popups).
askable(system_freezing).
askable(slow_downloads).
askable(anitivirus_installed).
askable(sluggish_performance).



Query to run program:
?- solve(customer_care(Issue)).
