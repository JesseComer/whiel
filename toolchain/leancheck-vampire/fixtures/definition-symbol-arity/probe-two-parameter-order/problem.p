% Minimal probe for the introduced-definition-symbol binder order.
%
% The conjecture's goal subterm `f(Y, g(X))` visits Y before X, so the
% twee goal transformation gives the symbol it introduces the parameter
% order (Y, X): the second parameter has the lower variable index. An
% emitter that sorts the `let` binders by variable index permutes them
% against the defining equation and the `rfl` no longer type-checks.
fof(ax, axiom, ! [A,B] : p(f(A,B))).
fof(conjecture, conjecture, ? [X,Y] : p(f(Y,g(X)))).
