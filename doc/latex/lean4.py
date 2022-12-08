# -*- coding: utf-8 -*-
"""
    pygments.lexers.theorem
    ~~~~~~~~~~~~~~~~~~~~~~~

    Lexers for theorem-proving languages.

    :copyright: Copyright 2006-2017 by the Pygments team, see AUTHORS.
    :license: BSD, see LICENSE for details.
"""

import re

from pygments.lexer import RegexLexer, default, words
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation, Generic

__all__ = ['Lean4Lexer']

class Lean4Lexer(RegexLexer):
    """
    For the `Lean 4 <https://github.com/leanprover/lean4>`_
    theorem prover.

    .. versionadded:: 2.0
    """
    name = 'Lean4'
    aliases = ['lean4']
    filenames = ['*.lean']
    mimetypes = ['text/x-lean']

    flags = re.MULTILINE | re.UNICODE

    keywords1 = (
        'import', 'abbreviation', 'opaque_hint', 'tactic_hint', 'definition',
        'renaming', 'inline', 'hiding', 'parameter', 'lemma', 'variable',
        'theorem', 'axiom', 'inductive', 'structure', 'universe', 'alias',
        'help', 'options', 'precedence', 'postfix', 'prefix',
        'infix', 'infixl', 'infixr', 'notation', '#eval',
        '#check', '#reduce', '#exit', 'coercion', 'end', 'private', 'using', 'namespace',
        'including', 'instance', 'section', 'context', 'protected', 'expose',
        'export', 'set_option', 'extends', 'open', 'example',
        'constant', 'constants', 'print', 'opaque', 'reducible', 'irreducible',
        'def', 'macro', 'elab', 'syntax', 'macro_rules', 'reduce', 'where',
        'abbrev', 'noncomputable', 'class', 'attribute', 'synth', 'mutual',
    )

    keywords2 = (
        'forall', 'fun', 'Pi', 'obtain', 'from', 'have', 'show', 'assume',
        'take', 'let', 'if', 'else', 'then', 'by', 'in', 'with', 'begin',
        'proof', 'qed', 'calc', 'match', 'nomatch', 'do', 'at',
    )

    keywords3 = (
        # Sorts
        'Type', 'Prop', 'Sort',
    )

    operators = (
        u'!=', u'#', u'&', u'&&', u'*', u'+', u'-', u'/', u'@', u'!', u'`',
        u'-.', u'->', u'.', u'..', u'...', u'::', u':>', u';', u';;', u'<',
        u'<-', u'=', u'==', u'>', u'_', u'|', u'||', u'~', u'=>', u'<=', u'>=',
        u'/\\', u'\\/', u'∀', u'Π', u'λ', u'↔', u'∧', u'∨', u'≠', u'≤', u'≥',
        u'¬', u'⁻¹', u'⬝', u'▸', u'→', u'∃', u'ℕ', u'ℤ', u'≈', u'×', u'⌞',
        u'⌟', u'≡', u'⟨', u'⟩',
    )

    punctuation = (u'(', u')', u':', u'{', u'}', u'[', u']', u'⦃', u'⦄',
                   u':=', u',')

    tokens = {
        'root': [
            (r'\s+', Text),
            (r'/-', Comment, 'comment'),
            (r'--.*?$', Comment.Single),
            (words(keywords1, prefix=r'\b', suffix=r'\b'), Keyword.Namespace),
            (words(keywords2, prefix=r'\b', suffix=r'\b'), Keyword),
            (words(keywords3, prefix=r'\b', suffix=r'\b'), Keyword.Type),
            (words(operators), Name.Builtin.Pseudo),
            (words(punctuation), Operator),
            (u"[A-Za-z_\u03b1-\u03ba\u03bc-\u03fb\u1f00-\u1ffe\u2100-\u214f]"
             u"[A-Za-z_'\u03b1-\u03ba\u03bc-\u03fb\u1f00-\u1ffe\u2070-\u2079"
             u"\u207f-\u2089\u2090-\u209c\u2100-\u214f0-9]*", Name),
            (r'\d+', Number.Integer),
            (r'"', String.Double, 'string'),
            (r'[~?][a-z][\w\']*:', Name.Variable)
        ],
        'comment': [
            # Multiline Comments
            (r'[^/-]', Comment.Multiline),
            (r'/-', Comment.Multiline, '#push'),
            (r'-/', Comment.Multiline, '#pop'),
            (r'[/-]', Comment.Multiline)
        ],
        'string': [
            (r'[^\\"]+', String.Double),
            (r'\\[n"\\]', String.Escape),
            ('"', String.Double, '#pop'),
        ],
    }
