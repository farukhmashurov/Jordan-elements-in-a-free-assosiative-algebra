(* ::Package:: *)

(*
  JordanCriterion.wl

  Exact membership criterion for Jordan elements in a free associative
  algebra, following F. A. Mashurov and B. K. Sartayev.

  This file is intended to be the version-controlled source. Load it with

      Get["/absolute/path/to/JordanCriterion.wl"];

  and then run JordanSelfTest[] before using it in a new Mathematica version.
*)

$JordanCriterionVersion = "1.1.0";

ClearAll[
  Compositions12, JordanSetup, JordanU, JordanMinimalPolynomial,
  JordanCriterionPolynomial, JordanCharacteristicPolynomial,
  JordanDimension, JordanProject, JordanElementQ, JordanExpression,
  JordanReport, JordanSelfTest, w,
  canonComposition, collectTerms, jordanTerms, blockTerms, TTerms,
  tMatrix, leadingCoefficient, squareFreeMonic, krylovMinPoly, annihilatesQ,
  JordanMinimalPolynomialRaw, digitsValue, parseExactRational,
  parseStringTerm, parseJordanString, normalizeWord, wordList, wordLabel,
  toVector, fromVector, jordanPowers, applyPoly, jordanMonomialString
];

JordanSetup::usage =
  "JordanSetup[n] constructs and caches the word basis, the operators T_lambda, and U_n.";
JordanU::usage =
  "JordanU[n] gives the exact matrix U_n on the multilinear component V_n.";
JordanMinimalPolynomial::usage =
  "JordanMinimalPolynomial[n, x] gives the minimal polynomial of U_n.";
JordanCriterionPolynomial::usage =
  "JordanCriterionPolynomial[n, x] gives the square-free criterion polynomial p_n.";
JordanCharacteristicPolynomial::usage =
  "JordanCharacteristicPolynomial[n, x] gives an Association containing det(x I-U_n), e_n, and q_n.";
JordanDimension::usage =
  "JordanDimension[n] gives dim V_n, e_n, and dim(J intersect V_n).";
JordanElementQ::usage =
  "JordanElementQ[n, f] returns True exactly when the multilinear polynomial f is Jordan.";
JordanProject::usage =
  "JordanProject[n, f] gives the Jordan projection f Pi_n.";
JordanExpression::usage =
  "JordanExpression[n, f] expresses a Jordan element as a list of Jordan monomial data.";
JordanReport::usage =
  "JordanReport[n, f] prints the complete criterion calculation and returns its data as an Association.";
JordanSelfTest::usage =
  "JordanSelfTest[] checks dimensions, characteristic polynomials, criterion polynomials, examples, and parsing through n=5.";
w::usage =
  "w[word] denotes an associative word, for example w[1234] or w[{1,2,3,4}].";

JordanMinimalPolynomialRaw::prob =
  "The large-degree Krylov computation did not obtain a fully confirmed candidate after all configured attempts.";
parseJordanString::syntax =
  "Could not parse the string input. Use terms such as 1234, -1234, or 3/2*1234, separated by + or -.";
toVector::word =
  "At least one word label is not a permutation of 1 through n.";
toVector::form =
  "The input must be a linear combination of w[word] terms, a supported string, or a list of word->coefficient rules.";
toVector::exact =
  "Use exact coefficients such as 1/2, not machine-precision decimals such as 0.5.";

(* For matrices through 120 by 120, compute the exact characteristic
   polynomial and take its square-free part. This makes n <= 5 fully
   deterministic and also cross-checks the characteristic data. *)
$JordanExactCharacteristicDimension = 120;
$JordanKrylovPrime = 2147483629;
$JordanKrylovAttempts = 6;

(* ------------------------------------------------------------------ *)
(* 1. Compositions of n with parts 1 and 2                            *)
(* ------------------------------------------------------------------ *)

Compositions12[0] = {{}};
Compositions12[n_Integer?Positive] := Compositions12[n] =
  Join[
    Prepend[#, 1] & /@ Compositions12[n - 1],
    If[n >= 2, Prepend[#, 2] & /@ Compositions12[n - 2], {}]
  ];

(* T_(1,1,mu) and T_(2,mu) are equal. *)
canonComposition[lam_List] :=
  If[
    Length[lam] >= 2 && lam[[1]] == 1 && lam[[2]] == 1,
    Prepend[Drop[lam, 2], 2],
    lam
  ];

(* ------------------------------------------------------------------ *)
(* 2. Expansion of T_lambda in the associative word basis             *)
(* ------------------------------------------------------------------ *)

collectTerms[terms_List] :=
  DeleteCases[
    List @@@ Normal[Merge[Apply[Rule, terms, {1}], Total]],
    {_, 0}
  ];

jordanTerms[p_List, q_List] :=
  collectTerms[
    Flatten[
      Table[
        {
          {Join[p[[i, 1]], q[[j, 1]]], p[[i, 2]] q[[j, 2]]/2},
          {Join[q[[j, 1]], p[[i, 1]]], p[[i, 2]] q[[j, 2]]/2}
        },
        {i, Length[p]}, {j, Length[q]}
      ],
      2
    ]
  ];

blockTerms[b_List] :=
  If[
    Length[b] == 1,
    {{b, 1}},
    {{b, 1/2}, {Reverse[b], 1/2}}
  ];

TTerms[lam_List] := TTerms[lam] = Module[{factors},
  factors = blockTerms /@ TakeList[Range[Total[lam]], lam];
  Fold[jordanTerms, First[factors], Rest[factors]]
];

(* ------------------------------------------------------------------ *)
(* 3. Matrix of 2^(n-1) T_lambda on V_n                               *)
(*    Rows are input words, columns are output words; action is right. *)
(* ------------------------------------------------------------------ *)

tMatrix[n_Integer, lam_List, basis_List, index_Association] :=
  Module[{d = Length[basis], terms, rules, scale = 2^(n - 1)},
    terms = TTerms[lam];
    rules = Flatten[
      Table[
        Module[{perm, coefficient, columns},
          perm = terms[[k, 1]];
          coefficient = scale terms[[k, 2]];
          columns = Lookup[index, Key /@ basis[[All, perm]]];
          Table[{i, columns[[i]]} -> coefficient, {i, d}]
        ],
        {k, Length[terms]}
      ],
      1
    ];
    SparseArray[
      DeleteCases[Normal[Merge[rules, Total]], _ -> 0],
      {d, d}
    ]
  ];

(* ------------------------------------------------------------------ *)
(* 4. Setup for degree n                                               *)
(* ------------------------------------------------------------------ *)

JordanSetup[n_Integer?Positive] := JordanSetup[n] =
  Module[{basis, d, index, compositions, multiplicities, keys, matrices, uint},
    basis = Permutations[Range[n]];
    d = Length[basis];
    index = AssociationThread[basis -> Range[d]];
    compositions = Compositions12[n];
    multiplicities = Counts[canonComposition /@ compositions];
    keys = Keys[multiplicities];
    matrices = AssociationThread[
      keys -> (tMatrix[n, #, basis, index] & /@ keys)
    ];
    uint = Total[
      Table[
        Lookup[multiplicities, Key[key]]
          Transpose[Lookup[matrices, Key[key]]]
          . Lookup[matrices, Key[key]],
        {key, keys}
      ]
    ];
    <|
      "n" -> n,
      "d" -> d,
      "basis" -> basis,
      "index" -> index,
      "compositions" -> compositions,
      "multiplicities" -> multiplicities,
      "scale" -> 4^(n - 1),
      "T" -> matrices,
      "Uint" -> uint,
      "U" -> uint/4^(n - 1)
    |>
  ];

JordanU[n_Integer?Positive] := JordanSetup[n]["U"];

(* ------------------------------------------------------------------ *)
(* 5. Characteristic, minimal, and criterion polynomials               *)
(* ------------------------------------------------------------------ *)

JordanCharacteristicPolynomial[n_Integer?Positive, x_: t] :=
  JordanCharacteristicPolynomial[n, x] =
    Module[{state = JordanSetup[n], characteristic, coefficients, e},
      characteristic = CharacteristicPolynomial[state["U"], x];
      coefficients = CoefficientList[characteristic, x];

      (* LengthWhile is intentional. Searching with FirstPosition and an
         explicit level can match the head List at position {0}, which was
         the source of the e_n = -1 bug in the original notebook. *)
      e = LengthWhile[coefficients, (# === 0) &];

      <|
        "characteristic" -> characteristic,
        "e" -> e,
        "q" -> Factor[Cancel[characteristic/x^e]]
      |>
    ];

leadingCoefficient[polynomial_, x_Symbol] :=
  Coefficient[polynomial, x, Exponent[polynomial, x]];

squareFreeMonic[polynomial_, x_Symbol] :=
  Module[{squareFree},
    squareFree = Cancel[
      polynomial/PolynomialGCD[polynomial, D[polynomial, x]]
    ];
    Expand[squareFree/leadingCoefficient[squareFree, x]]
  ];

(* A cyclic-vector polynomial of the integer-scaled matrix. The degree is
   discovered modulo a large prime and its coefficients are then solved
   exactly over the rationals. *)
krylovMinPoly[uint_, d_Integer, x_Symbol, seed_Integer] :=
  Module[{v, rowsMod, next, degree, rowsExact, matrix, solution},
    v = BlockRandom[
      SeedRandom[seed];
      RandomInteger[{-9, 9}, d]
    ];
    If[v === ConstantArray[0, d], v = ConstantArray[1, d]];

    rowsMod = {Mod[v, $JordanKrylovPrime]};
    While[True,
      next = Mod[Normal[Last[rowsMod] . uint], $JordanKrylovPrime];
      If[
        MatrixRank[
          Append[rowsMod, next],
          Modulus -> $JordanKrylovPrime
        ] == Length[rowsMod],
        Break[]
      ];
      AppendTo[rowsMod, next]
    ];

    degree = Length[rowsMod];
    rowsExact = NestList[Normal[# . uint] &, v, degree];
    matrix = Transpose[Most[rowsExact]];
    solution = Quiet[Check[LinearSolve[matrix, Last[rowsExact]], $Failed]];
    If[
      solution === $Failed,
      $Failed,
      Expand[x^degree - Sum[solution[[i]] x^(i - 1), {i, degree}]]
    ]
  ];

annihilatesQ[uint_, polynomial_, x_Symbol, vector_List] :=
  Module[{coefficients, accumulator, current},
    coefficients = CoefficientList[polynomial, x];
    current = vector;
    accumulator = coefficients[[1]] vector;
    Do[
      current = Normal[current . uint];
      accumulator = accumulator + coefficients[[i + 1]] current,
      {i, Length[coefficients] - 1}
    ];
    accumulator === ConstantArray[0, Length[vector]]
  ];

JordanMinimalPolynomialRaw[n_Integer?Positive] :=
  JordanMinimalPolynomialRaw[n] =
    Module[
      {state, uint, d, scale, characteristic, candidate = 1,
       cyclic, confirmed = False, testVectors, attempts},

      state = JordanSetup[n];
      uint = state["Uint"];
      d = state["d"];
      scale = state["scale"];

      If[
        d <= $JordanExactCharacteristicDimension,
        characteristic =
          JordanCharacteristicPolynomial[n, jt]["characteristic"];
        Return[squareFreeMonic[characteristic, jt]]
      ];

      attempts = $JordanKrylovAttempts;
      Do[
        cyclic = krylovMinPoly[
          uint, d, jx, 20260908 + 1009 attempt
        ];
        If[cyclic =!= $Failed,
          candidate = PolynomialLCM[candidate, cyclic];
          candidate = Expand[
            candidate/leadingCoefficient[candidate, jx]
          ];
        ];

        testVectors = BlockRandom[
          SeedRandom[31082026 + 101 attempt];
          Table[RandomInteger[{-9, 9}, d], {6}]
        ];
        confirmed =
          cyclic =!= $Failed &&
          And @@ (annihilatesQ[uint, candidate, jx, #] & /@ testVectors);
        If[confirmed, Break[]],
        {attempt, 1, attempts}
      ];

      If[! confirmed, Message[JordanMinimalPolynomialRaw::prob]];

      Expand[
        (candidate /. jx -> scale jt)/
          scale^Exponent[candidate, jx]
      ]
    ];

JordanMinimalPolynomial[n_Integer?Positive, x_: t] :=
  Expand[JordanMinimalPolynomialRaw[n] /. jt -> x];

JordanCriterionPolynomial[n_Integer?Positive, x_: t] :=
  Module[{minimal, criterion},
    minimal = JordanMinimalPolynomialRaw[n];
    criterion =
      If[
        TrueQ[(minimal /. jt -> 0) == 0],
        Cancel[minimal/jt],
        minimal
      ];
    Expand[criterion /. jt -> x]
  ];

JordanDimension[n_Integer?Positive] := JordanDimension[n] =
  Module[{state = JordanSetup[n], rank},
    rank =
      If[
        state["d"] <= $JordanExactCharacteristicDimension,
        MatrixRank[state["Uint"]],
        MatrixRank[state["Uint"], Modulus -> $JordanKrylovPrime]
      ];
    <|
      "dimV" -> state["d"],
      "e" -> state["d"] - rank,
      "dimJ" -> rank
    |>
  ];

(* ------------------------------------------------------------------ *)
(* 6. Validated input and output of multilinear elements               *)
(* ------------------------------------------------------------------ *)

digitsValue[s_String] := FromDigits[ToCharacterCode[s] - 48];

parseExactRational[s_String] :=
  Module[{sign = 1, body = s, pieces, numerator, denominator = 1},
    If[StringStartsQ[body, "+"], body = StringDrop[body, 1]];
    If[
      StringStartsQ[body, "-"],
      sign = -1;
      body = StringDrop[body, 1]
    ];
    If[
      ! StringMatchQ[
        body,
        DigitCharacter .. ~~ ("/" ~~ DigitCharacter ..) ...
      ],
      Return[$Failed]
    ];
    pieces = StringSplit[body, "/"];
    If[Length[pieces] > 2, Return[$Failed]];
    numerator = digitsValue[pieces[[1]]];
    If[Length[pieces] == 2, denominator = digitsValue[pieces[[2]]]];
    If[denominator == 0, Return[$Failed]];
    sign numerator/denominator
  ];

parseStringTerm[token_String] :=
  Module[{pieces, coefficient, wordText},
    pieces = StringSplit[token, "*"];
    Switch[
      Length[pieces],
      1,
        coefficient = 1;
        wordText = pieces[[1]];
        If[
          StringStartsQ[wordText, "+"],
          wordText = StringDrop[wordText, 1]
        ];
        If[
          StringStartsQ[wordText, "-"],
          coefficient = -1;
          wordText = StringDrop[wordText, 1]
        ],
      2,
        coefficient = parseExactRational[pieces[[1]]];
        wordText = pieces[[2]],
      _,
        Return[$Failed]
    ];
    If[
      coefficient === $Failed ||
        ! StringMatchQ[wordText, DigitCharacter ..],
      Return[$Failed]
    ];
    digitsValue[wordText] -> coefficient
  ];

parseJordanString[s_String] :=
  Module[{compact, tokens, pairs},
    compact = StringDelete[s, WhitespaceCharacter];
    If[compact == "0", Return[{}]];
    tokens = DeleteCases[
      StringSplit[StringReplace[compact, "-" -> "+-"], "+"],
      ""
    ];
    If[tokens === {}, Message[parseJordanString::syntax]; Return[$Failed]];
    pairs = parseStringTerm /@ tokens;
    If[
      MemberQ[pairs, $Failed],
      Message[parseJordanString::syntax];
      $Failed,
      pairs
    ]
  ];

wordList[k_Integer] := IntegerDigits[k];
wordList[list_List] /; VectorQ[list, IntegerQ] := list;
wordList[_] := $Failed;

normalizeWord[n_Integer?Positive, label_] :=
  Module[{word = wordList[label]},
    If[
      word =!= $Failed && Sort[word] === Range[n],
      word,
      $Failed
    ]
  ];

wordLabel[word_List] :=
  If[Max[word] <= 9, FromDigits[word], word];

toVector[n_Integer?Positive, f_String] :=
  Module[{parsed = parseJordanString[f]},
    If[parsed === $Failed, $Failed, toVector[n, parsed]]
  ];

toVector[n_Integer?Positive, f_List] /; MatchQ[f, {___Rule}] :=
  Module[{state = JordanSetup[n], pairs, words, bad, vector, position},
    pairs = ({First[#], Last[#]} & /@ f);
    words = normalizeWord[n, #] & /@ pairs[[All, 1]];
    bad = Pick[pairs[[All, 1]], (# === $Failed) & /@ words];
    If[
      bad =!= {},
      Message[toVector::word];
      Return[$Failed]
    ];
    If[
      ! FreeQ[pairs[[All, 2]], HoldPattern[w[___]]],
      Message[toVector::form];
      Return[$Failed]
    ];
    If[
      ! FreeQ[pairs[[All, 2]], _?InexactNumberQ],
      Message[toVector::exact];
      Return[$Failed]
    ];

    vector = ConstantArray[0, state["d"]];
    Do[
      position = Lookup[state["index"], Key[words[[i]]]];
      vector[[position]] += pairs[[i, 2]],
      {i, Length[pairs]}
    ];
    vector
  ];

toVector[n_Integer?Positive, f_] :=
  Module[{state = JordanSetup[n], expression, arguments, words, bad,
          reconstructed, vector},
    expression = Expand[f];
    If[
      ! FreeQ[expression, _?InexactNumberQ],
      Message[toVector::exact];
      Return[$Failed]
    ];
    arguments = DeleteDuplicates[
      Cases[
        expression,
        HoldPattern[w[label_]] :> label,
        {0, Infinity}
      ]
    ];
    words = normalizeWord[n, #] & /@ arguments;
    bad = Pick[arguments, (# === $Failed) & /@ words];
    If[
      bad =!= {},
      Message[toVector::word];
      Return[$Failed]
    ];

    reconstructed = Total[
      Table[
        Coefficient[expression, w[label]] w[label],
        {label, arguments}
      ]
    ];
    If[
      Expand[expression - reconstructed] =!= 0,
      Message[toVector::form];
      Return[$Failed]
    ];

    vector = ConstantArray[0, state["d"]];
    Do[
      vector[[
        Lookup[state["index"], Key[words[[i]]]]
      ]] += Coefficient[expression, w[arguments[[i]]]],
      {i, Length[arguments]}
    ];
    vector
  ];

fromVector[n_Integer?Positive, vector_List] :=
  Module[{state = JordanSetup[n]},
    Total[
      Table[
        If[
          vector[[i]] === 0,
          0,
          vector[[i]] w[wordLabel[state["basis"][[i]]]]
        ],
        {i, state["d"]}
      ]
    ]
  ];

(* ------------------------------------------------------------------ *)
(* 7. Applying U_n and polynomials in U_n                              *)
(* ------------------------------------------------------------------ *)

jordanPowers[n_Integer?Positive, vector_List, k_Integer?NonNegative] :=
  Module[{state = JordanSetup[n], scale},
    scale = state["scale"];
    Rest[
      NestList[
        Normal[# . state["Uint"]]/scale &,
        vector,
        k
      ]
    ]
  ];

applyPoly[n_Integer?Positive, vector_List, polynomial_, x_Symbol] :=
  Module[{coefficients, state = JordanSetup[n], accumulator, current, scale},
    coefficients = CoefficientList[polynomial, x];
    scale = state["scale"];
    current = vector;
    accumulator = coefficients[[1]] vector;
    Do[
      current = Normal[current . state["Uint"]]/scale;
      accumulator = accumulator + coefficients[[i + 1]] current,
      {i, Length[coefficients] - 1}
    ];
    accumulator
  ];

(* ------------------------------------------------------------------ *)
(* 8. Membership test, projection, and Jordan expression               *)
(* ------------------------------------------------------------------ *)

JordanElementQ[n_Integer?Positive, f_] :=
  Module[{vector = toVector[n, f], criterion},
    If[vector === $Failed, Return[$Failed]];
    criterion = JordanCriterionPolynomial[n, jt];
    applyPoly[n, vector, criterion, jt] ===
      ConstantArray[0, Length[vector]]
  ];

JordanProject[n_Integer?Positive, f_] :=
  Module[{vector = toVector[n, f], criterion, constant},
    If[vector === $Failed, Return[$Failed]];
    criterion = JordanCriterionPolynomial[n, jt];
    constant = criterion /. jt -> 0;
    fromVector[
      n,
      vector - applyPoly[n, vector, criterion, jt]/constant
    ]
  ];

jordanMonomialString[composition_List, word_List] :=
  Module[{blocks, parts, current},
    blocks = TakeList[word, composition];
    parts = Map[
      If[
        Length[#] == 1,
        "z" <> ToString[#[[1]]],
        "(z" <> ToString[#[[1]]] <>
          " o z" <> ToString[#[[2]]] <> ")"
      ] &,
      blocks
    ];
    current = First[parts];
    Do[
      current = "(" <> current <> " o " <> parts[[i]] <> ")",
      {i, 2, Length[parts]}
    ];
    current
  ];

JordanExpression[n_Integer?Positive, f_] :=
  Module[
    {state = JordanSetup[n], vector = toVector[n, f], criterion,
     constant, quotient, preimage, output = {}, coefficients, scale},

    If[vector === $Failed, Return[$Failed]];
    criterion = JordanCriterionPolynomial[n, jt];
    constant = criterion /. jt -> 0;
    quotient = Cancel[(criterion - constant)/jt];
    preimage = -applyPoly[n, vector, quotient, jt]/constant;

    If[
      Normal[preimage . state["Uint"]]/state["scale"] =!= vector,
      Return[$Failed]
    ];

    scale = 2^(n - 1);
    Do[
      coefficients =
        Lookup[state["multiplicities"], Key[composition]]
          Normal[
            preimage .
              Transpose[Lookup[state["T"], Key[composition]]]
          ]/scale;
      Do[
        If[
          coefficients[[i]] =!= 0,
          AppendTo[
            output,
            {coefficients[[i]], composition, state["basis"][[i]]}
          ]
        ],
        {i, state["d"]}
      ],
      {composition, Keys[state["multiplicities"]]}
    ];
    output
  ];

(* ------------------------------------------------------------------ *)
(* 9. Full report                                                      *)
(* ------------------------------------------------------------------ *)

ClearAll[ShowMatrix, MaxTerms, ComputeQ, ShowJordanExpression];
Options[JordanReport] = {
  ShowMatrix -> Automatic,
  MaxTerms -> 24,
  ComputeQ -> Automatic,
  ShowJordanExpression -> False,
  "ShowMatrix" -> Inherited,
  "MaxTerms" -> Inherited,
  "ComputeQ" -> Inherited,
  "ShowJordanExpression" -> Inherited
};

JordanReport[n_Integer?Positive, f_, OptionsPattern[]] :=
  Module[
    {state, vector, criterion, constant, degree, powers, residual,
     jordanQ, dimensions, characteristicData, showMatrix, maxTerms,
     computeQ, preimage, quotient, line, display, expression, i,
     preimageQ, method, showExpression},

    state = JordanSetup[n];
    vector = toVector[n, f];
    If[vector === $Failed, Return[$Failed]];

    showMatrix =
      If[
        OptionValue["ShowMatrix"] === Inherited,
        OptionValue[ShowMatrix],
        OptionValue["ShowMatrix"]
      ] /. Automatic -> (state["d"] <= 24);
    maxTerms =
      If[
        OptionValue["MaxTerms"] === Inherited,
        OptionValue[MaxTerms],
        OptionValue["MaxTerms"]
      ];
    If[! IntegerQ[maxTerms] || maxTerms < 0, maxTerms = 24];
    computeQ =
      If[
        OptionValue["ComputeQ"] === Inherited,
        OptionValue[ComputeQ],
        OptionValue["ComputeQ"]
      ] /. Automatic -> (state["d"] <= 24);
    showExpression =
      If[
        OptionValue["ShowJordanExpression"] === Inherited,
        OptionValue[ShowJordanExpression],
        OptionValue["ShowJordanExpression"]
      ];
    method =
      If[
        state["d"] <= $JordanExactCharacteristicDimension,
        "exact characteristic polynomial",
        "Krylov candidate with exact rational coefficients"
      ];
    line = "----------------------------------------------------------------";

    display[values_] :=
      Module[{nonzero = Count[values, Except[0]]},
        If[
          nonzero <= maxTerms,
          fromVector[n, values],
          Row[{
            "(", nonzero,
            " nonzero coefficients; suppressed - see the returned Association)"
          }]
        ]
      ];

    Print[line];
    Print["DEGREE n = ", n];
    Print[line];
    Print["implementation version = ", $JordanCriterionVersion];
    Print["criterion method = ", method];
    Print["dim V_n = n! = ", state["d"]];
    Print[
      "compositions C_n (", Length[state["compositions"]], " of them): ",
      If[n <= 6, state["compositions"], Short[state["compositions"], 3]]
    ];
    Print[
      "distinct T_lambda operators with multiplicities ",
      "(T_(1,1,mu) = T_(2,mu)):"
    ];
    Print["   ", Normal[state["multiplicities"]]];

    Print[line];
    Print["THE OPERATOR U_n = Sum_lambda m_lambda T_lambda^dagger T_lambda"];
    dimensions = JordanDimension[n];
    Print["rank U_n = dim (J intersect V_n) = ", dimensions["dimJ"]];
    Print["e_n = multiplicity of eigenvalue 0 = ", dimensions["e"]];
    Print[
      "largest eigenvalue of U_n = |C_n| = ",
      Length[state["compositions"]]
    ];
    If[
      TrueQ[showMatrix],
      Print["U_n = "];
      Print[MatrixForm[Normal[state["U"]]]],
      Print["(matrix suppressed; it is the key U in the returned Association)"]
    ];

    Print[line];
    Print["THE CRITERION POLYNOMIAL"];
    criterion = JordanCriterionPolynomial[n, jt];
    degree = Exponent[criterion, jt];
    Print[
      "minimal polynomial of U_n: m_n(t) = ",
      Factor[JordanMinimalPolynomial[n, jt]] /. jt -> t
    ];
    Print["criterion polynomial p_n(t) = m_n(t)/t, factored:"];
    Print["   p_n(t) = ", Factor[criterion] /. jt -> t];
    Print[
      "   expanded: p_n(t) = ",
      Collect[criterion, jt] /. jt -> t
    ];
    Print[
      "   deg p_n = ", degree,
      " (so the powers below run through U_n^", degree, ")"
    ];

    If[
      TrueQ[computeQ],
      characteristicData = JordanCharacteristicPolynomial[n, jt];
      Print[
        "det(t I - U_n) = t^", characteristicData["e"], " q_n(t)"
      ];
      Print[
        "   q_n(t) = ",
        characteristicData["q"] /. jt -> t
      ];
      Print[
        "   deg q_n = ",
        Exponent[characteristicData["q"], jt],
        " (p_n is its square-free part)"
      ],
      Print[
        "(q_n not printed; use ComputeQ -> True to print it. ",
        "Exact computation is practical through n = 5.)"
      ]
    ];

    Print[line];
    Print["THE ELEMENT"];
    Print["f = ", fromVector[n, vector]];
    powers = jordanPowers[n, vector, degree];
    Print[line];
    Print["THE POWERS f U_n^k"];
    Do[
      Print["f U_n^", i, " = ", display[powers[[i]]]],
      {i, degree}
    ];

    Print[line];
    Print["SUBSTITUTION INTO THE CRITERION"];
    residual = applyPoly[n, vector, criterion, jt];
    Print["f p_n(U_n) = ", display[residual]];
    jordanQ = residual === ConstantArray[0, state["d"]];

    Print[line];
    constant = criterion /. jt -> 0;
    quotient = Cancel[(criterion - constant)/jt];
    preimage = -applyPoly[n, vector, quotient, jt]/constant;
    preimageQ =
      Normal[preimage . state["Uint"]]/state["scale"] === vector;
    Print[
      "preimage check b U_n = f (equivalent to the verdict): ",
      preimageQ
    ];
    Print[
      "projection f Pi_n = ",
      display[vector - residual/constant]
    ];
    If[
      ! jordanQ,
      Print["obstruction f - f Pi_n = ", display[residual/constant]]
    ];

    If[
      TrueQ[showExpression] && jordanQ,
      expression = JordanExpression[n, f];
      Print[line];
      Print[
        "f as a Jordan polynomial (", Length[expression], " terms):"
      ];
      Do[
        Print[
          "   ", expression[[i, 1]], " * ",
          jordanMonomialString[
            expression[[i, 2]], expression[[i, 3]]
          ]
        ],
        {i, Min[Length[expression], 200]}
      ]
    ];

    Print[line];
    Print[
      If[
        jordanQ,
        "RESULT: f IS a Jordan element.",
        "RESULT: f is NOT a Jordan element."
      ]
    ];
    Print[line];

    <|
      "version" -> $JordanCriterionVersion,
      "n" -> n,
      "f" -> vector,
      "U" -> state["U"],
      "Uint" -> state["Uint"],
      "p" -> (criterion /. jt -> t),
      "degp" -> degree,
      "m" -> (JordanMinimalPolynomial[n, jt] /. jt -> t),
      "powers" -> powers,
      "substitution" -> residual,
      "projection" -> vector - residual/constant,
      "dimensions" -> dimensions,
      "JordanQ" -> jordanQ,
      "criterionMethod" -> method
    |>
  ];

(* ------------------------------------------------------------------ *)
(* 10. Regression tests through degree five                            *)
(* ------------------------------------------------------------------ *)

JordanSelfTest[] :=
  Module[
    {ok = True, check, expectedDimensions, characteristicData,
     squareFreeQ, projected},

    check[name_, value_, expected_] := (
      Print[
        If[value === expected, "PASS  ", "FAIL  "],
        name,
        If[
          value === expected,
          "",
          Row[{"   got ", value, " expected ", expected}]
        ]
      ];
      If[value =!= expected, ok = False]
    );

    expectedDimensions = <|
      1 -> {1, 0, 1},
      2 -> {2, 1, 1},
      3 -> {6, 3, 3},
      4 -> {24, 13, 11},
      5 -> {120, 65, 55}
    |>;

    Do[
      check[
        "dimensions for n = " <> ToString[n],
        {
          JordanDimension[n]["dimV"],
          JordanDimension[n]["e"],
          JordanDimension[n]["dimJ"]
        },
        Lookup[expectedDimensions, n]
      ],
      {n, 1, 5}
    ];

    Do[
      characteristicData = JordanCharacteristicPolynomial[n, jt];
      check[
        "characteristic zero multiplicity e_" <> ToString[n],
        characteristicData["e"],
        JordanDimension[n]["e"]
      ];
      check[
        "degree q_" <> ToString[n],
        Exponent[characteristicData["q"], jt],
        JordanDimension[n]["dimJ"]
      ];
      squareFreeQ = squareFreeMonic[characteristicData["q"], jt];
      check[
        "p_" <> ToString[n] <> " is square-free(q_" <>
          ToString[n] <> ")",
        Expand[JordanCriterionPolynomial[n, jt] - squareFreeQ],
        0
      ],
      {n, 1, 5}
    ];

    check[
      "p_3(t)",
      Factor[JordanCriterionPolynomial[3, jt]],
      Factor[(jt - 3) (jt - 3/4)]
    ];
    check[
      "p_4(t)",
      Factor[JordanCriterionPolynomial[4, jt]],
      Factor[
        (jt - 5) (jt - 1/2) (jt - 9/4)
          (jt - 9/8) (jt - 3/8)
      ]
    ];

    check[
      "safe rational string parser",
      toVector[3, "1/2*123 - 1/2*321"],
      toVector[3, (w[123] - w[321])/2]
    ];
    check[
      "Example 5.2: 123 + 321 is Jordan",
      JordanElementQ[3, "123 + 321"],
      True
    ];
    check[
      "Example 5.4: 1234+4321+1243+3421 is Jordan",
      JordanElementQ[4, "1234 + 4321 + 1243 + 3421"],
      True
    ];
    check[
      "Example 5.6: the tetrad 1234 + 4321 is not Jordan",
      JordanElementQ[4, "1234 + 4321"],
      False
    ];
    check[
      "degree-five reverse pair 12345 + 54321 is not Jordan",
      JordanElementQ[5, "12345 + 54321"],
      False
    ];

    projected = JordanProject[5, "12345"];
    check[
      "the degree-five projection is Jordan",
      JordanElementQ[5, projected],
      True
    ];

    Print[If[ok, "ALL TESTS PASSED", "SOME TESTS FAILED"]];
    ok
  ];
