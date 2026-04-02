#!/usr/bin/env python3
"""
Count equations in the ETP catalog whose left-right mirror is not present.

The "mirror" of an equation is obtained by recursively swapping left and right
children at every binary operation node in both sides of the equation, then
renaming variables to canonical first-appearance order (x, y, z, w, u, ...).

For example:
    x ◇ y = x ◇ (y ◇ z)
    mirror tree:  y ◇ x = (z ◇ y) ◇ x
    canonicalized: x ◇ y = (z ◇ x) ◇ y

Usage:
    python3 count_mirrors.py [path/to/equations.txt]

If no path is given, looks for equations.txt in the current directory and
common project locations.
"""

import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Parser: equation string -> (lhs_tree, rhs_tree)
# Trees are either a variable name (str) or ('*', left, right).
# ---------------------------------------------------------------------------

def tokenize(s):
    tokens = []
    i = 0
    while i < len(s):
        if s[i] == ' ':
            i += 1
        elif s[i] in '()=':
            tokens.append(s[i]); i += 1
        elif s[i:i + len('◇')] == '◇':
            tokens.append('◇'); i += len('◇')
        elif s[i].isalpha():
            tokens.append(s[i]); i += 1
        else:
            i += 1
    return tokens


def _parse_expr(tokens, pos):
    left, pos = _parse_atom(tokens, pos)
    while pos < len(tokens) and tokens[pos] == '◇':
        right, pos = _parse_atom(tokens, pos + 1)
        left = ('*', left, right)
    return left, pos


def _parse_atom(tokens, pos):
    if tokens[pos] == '(':
        expr, pos = _parse_expr(tokens, pos + 1)
        assert tokens[pos] == ')', f"expected ')' at pos {pos}"
        return expr, pos + 1
    return tokens[pos], pos + 1


def parse_equation(eq_str):
    tokens = tokenize(eq_str)
    eq_idx = tokens.index('=')
    lhs, _ = _parse_expr(tokens, 0)
    rhs, _ = _parse_expr(tokens, eq_idx + 1)
    return lhs, rhs


# ---------------------------------------------------------------------------
# Mirror: recursively swap left <-> right children
# ---------------------------------------------------------------------------

def mirror_tree(tree):
    if isinstance(tree, str):
        return tree
    return ('*', mirror_tree(tree[2]), mirror_tree(tree[1]))


# ---------------------------------------------------------------------------
# Tree -> string (with minimal parentheses)
# ---------------------------------------------------------------------------

def tree_to_str(tree):
    """Convert tree to string matching ETP catalog parenthesization.

    The catalog uses explicit parens on both sides for any compound
    subexpression: (a ◇ b) ◇ c, not a ◇ b ◇ c.
    """
    if isinstance(tree, str):
        return tree
    l = tree_to_str(tree[1])
    r = tree_to_str(tree[2])
    if isinstance(tree[1], tuple):
        l = f"({l})"
    if isinstance(tree[2], tuple):
        r = f"({r})"
    return f"{l} ◇ {r}"


# ---------------------------------------------------------------------------
# Variable canonicalization: rename to first-appearance order (x, y, z, ...)
# ---------------------------------------------------------------------------

CANON_VARS = list('xyzwuv')


def canonicalize_vars(eq_str):
    """Rename single-letter variables to first-appearance order (x, y, z, w, u, v).

    The ETP catalog uses at most 6 distinct single-letter variables per equation.
    """
    mapping = {}
    idx = 0
    result = []
    for ch in eq_str:
        if ch.isalpha():
            if ch not in mapping:
                if idx >= len(CANON_VARS):
                    raise ValueError(
                        f"equation has more than {len(CANON_VARS)} variables: {eq_str}"
                    )
                mapping[ch] = CANON_VARS[idx]
                idx += 1
            result.append(mapping[ch])
        else:
            result.append(ch)
    return ''.join(result)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def find_equations_file(explicit_path=None):
    if explicit_path:
        return Path(explicit_path)
    candidates = [
        Path('equations.txt'),
        Path(__file__).resolve().parent.parent / 'equations.txt',
    ]
    for p in candidates:
        if p.exists():
            return p
    print("ERROR: equations.txt not found. Pass path as argument.", file=sys.stderr)
    sys.exit(1)


def mirror_equation(eq_str):
    """Return the canonicalized mirror of an equation string."""
    lhs, rhs = parse_equation(eq_str)
    m_lhs = mirror_tree(lhs)
    m_rhs = mirror_tree(rhs)
    raw = tree_to_str(m_lhs) + " = " + tree_to_str(m_rhs)
    return canonicalize_vars(raw)


def main():
    eq_path = find_equations_file(sys.argv[1] if len(sys.argv) > 1 else None)
    with open(eq_path) as f:
        equations = [line.strip() for line in f if line.strip()]

    eq_set = set(equations)

    self_mirror = []
    has_mirror = []
    no_mirror = []

    for i, eq in enumerate(equations):
        canon = mirror_equation(eq)
        if canon == eq:
            self_mirror.append(i + 1)
        elif canon in eq_set:
            has_mirror.append(i + 1)
        else:
            no_mirror.append(i + 1)

    print(f"Equations file: {eq_path} ({len(equations)} equations)")
    print(f"Self-mirror (chirally symmetric): {len(self_mirror)}")
    print(f"Has mirror in catalog:            {len(has_mirror)} ({len(has_mirror) // 2} pairs)")
    print(f"No mirror in catalog:             {len(no_mirror)}")
    print()

    if no_mirror:
        print(f"Equations without mirrors (first 20):")
        for eid in no_mirror[:20]:
            eq = equations[eid - 1]
            canon = mirror_equation(eq)
            print(f"  E{eid}: {eq}")
            print(f"    mirror: {canon}")
        if len(no_mirror) > 20:
            print(f"  ... and {len(no_mirror) - 20} more")
    print()

    # Classify by LHS type
    product_lhs = 0
    for eid in no_mirror:
        lhs, _ = parse_equation(equations[eid - 1])
        if isinstance(lhs, tuple):
            product_lhs += 1
    bare_lhs = len(no_mirror) - product_lhs
    print(f"Missing mirrors by LHS type:")
    print(f"  Product LHS (Family C): {product_lhs}")
    print(f"  Bare variable LHS:      {bare_lhs}")


if __name__ == '__main__':
    main()
