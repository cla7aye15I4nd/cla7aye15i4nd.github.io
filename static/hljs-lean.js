// Lean 4 language definition for highlight.js
hljs.registerLanguage('lean4', function(hljs) {
  const LEAN_KEYWORDS = {
    keyword: 'def theorem lemma example axiom constant abbrev structure class instance ' +
             'inductive where extends open namespace section end variable universe ' +
             'import export private protected partial unsafe noncomputable mutual ' +
             'attribute local macro macro_rules syntax elab deriving ' +
             'if then else match with do return let have this fun ' +
             'for in unless try catch finally throw assert dbg_trace sorry ' +
             'set_option by calc show assume suffices from',
    built_in: 'Type Prop Sort Nat Int Bool True False Unit PUnit ' +
              'Option Some None List Array String Char IO Monad Functor ' +
              'Eq Ne Lt Le Gt Ge And Or Not Iff Exists Subtype Sigma ' +
              'Decidable DecidableEq Inhabited Nonempty',
    literal: 'true false'
  };

  const LEAN_NUMBER = {
    className: 'number',
    variants: [
      { begin: '\\b0x[0-9a-fA-F]+' },
      { begin: '\\b0b[01]+' },
      { begin: '\\b0o[0-7]+' },
      { begin: '\\b[0-9]+\\.?[0-9]*' }
    ],
    relevance: 0
  };

  const LEAN_STRING = {
    className: 'string',
    variants: [
      { begin: '"', end: '"', contains: [{ begin: '\\\\.' }] },
      { begin: '\'', end: '\'' }
    ]
  };

  const LEAN_COMMENT = [
    hljs.COMMENT('--', '$'),
    hljs.COMMENT('/-', '-/', { contains: ['self'] })
  ];

  const LEAN_ATTRIBUTE = {
    className: 'meta',
    begin: '@\\[',
    end: '\\]',
    contains: [
      { className: 'keyword', begin: '\\b\\w+\\b' }
    ]
  };

  const LEAN_ANNOTATION = {
    className: 'meta',
    begin: '@',
    end: '(?=\\s|\\(|$)',
    contains: [
      { className: 'keyword', begin: '\\b\\w+(\\.\\w+)*\\b' }
    ]
  };

  const LEAN_TACTIC = {
    className: 'keyword',
    begin: '\\b(rfl|rw|simp|intro|intros|apply|exact|cases|induction|constructor|' +
           'ext|funext|congr|trivial|contradiction|exfalso|assumption|' +
           'decide|native_decide|norm_num|ring|linarith|omega|aesop|' +
           'rcases|obtain|use|refine|specialize|generalize|clear|rename|' +
           'have|let|show|suffices|calc|conv|focus|all_goals|any_goals|' +
           'repeat|first|try|skip|done|sorry|admit)\\b'
  };

  return {
    name: 'Lean 4',
    aliases: ['lean', 'lean4'],
    keywords: LEAN_KEYWORDS,
    contains: [
      ...LEAN_COMMENT,
      LEAN_STRING,
      LEAN_NUMBER,
      LEAN_ATTRIBUTE,
      LEAN_ANNOTATION,
      LEAN_TACTIC,
      {
        className: 'type',
        begin: '\\b[A-Z][a-zA-Z0-9_]*\\b',
        relevance: 0
      },
      {
        className: 'symbol',
        begin: '[→←↔∀∃λ∧∨¬≤≥≠⊆⊇∈∉∅∪∩⟨⟩⟪⟫▸◂⊢⊣×÷±∘∙·•]+'
      }
    ]
  };
});

// Also register as 'lean' alias
hljs.registerLanguage('lean', hljs.getLanguage('lean4'));
