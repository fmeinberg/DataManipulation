BeginPackge["DataManipulation`", {"ExpressionManipulation`"}]

TallyGrid::usage="";
RelativeFrequencies::usage="";
LabeledView::usage="";
DeleteBlankRows::usage="";
DeleteBlankColumns::usage="";
DeleteUnheadedColumns::usage="";
SquareTable::usage="";
MergeTables::usage="";
Pivot::usage="";

Begin["Private`"]

(* General *)

TallyGrid[data_] :=
    Grid[Reverse@
      SortBy[Tally[data], Last], Alignment -> Left,
     Frame -> All]

RelativeFrequencies[set_] :=
    With[ {l = Length[set]},
        ({#1[[1]],(#1[[2]])/l}&)/@Tally[set]
    ];

LabeledView[rules_] :=
    Labeled[Column@#2, #1, Top] & @@@ rules // SlideView

(* Table manipulation *)s

DeleteBlankRows[m_, blank_: ""] :=
    DeleteCases[m, {blank ..}];

DeleteBlankColumns[m_] :=
    Transpose@DeleteBlankRows@Transpose@m

DeleteBlankRowsAndColumns[m_] :=
    DeleteBlankColumns@DeleteBlankRows@m

DeleteUnheadedColumns[m_] :=
    Transpose@DeleteCases[Transpose@m, {"", ___}]

SquareTable[table_] :=
    With[ {max = Max[Length /@ table]},
        DeleteUnheadedColumns@
         DeleteBlankRowsAndColumns[PadRight[#, max, ""] & /@ table]
    ]

MergeTables[lists_, blank_:""] :=
    Block[ {t, allheaders},
        t[1] = Map[
          DeleteUnheadedColumns@
            DeleteBlankRowsAndColumns@
             Block[ {i = #, max},
                 max = Max[Length /@ i];
                 PadRight[#, max, ""] & /@ i
             ] &, lists];
        allheaders = Union@Flatten[t[1][[All, 1]]];
        t[2] = Function[item,
           Join[MapThread[Rule, {First@item, Transpose@Rest@item}],
            MapThread[
             Rule, {Complement[allheaders, First@item],
              Array[blank &, {Length@Complement[allheaders, First@item],
                Length@Rest@item}]}]]] /@ t[1];
        t[3] = Join @@ (DeleteCases[# /. t[2], #] ) & /@ allheaders;
        t[4] = Prepend[Transpose@t[3], allheaders]
    ]

 (* Pivoting Data *)

 Pivot[data_, heads_, pivots_List, goals_, foo_: Plus] :=
     Block[ {f, p, headerPos = PositionRules@heads,
       level = Length@pivots},
         Map[Rule[#[[1, pivots /. headerPos]],
            foo[#[[All, goals /. headerPos]]]] &,
          GatherBy[SortBy[data, #[[pivots /. headerPos]] &],
           Table[f[p[Slot[1], pivots[[i]] /. headerPos]], {i, 1,
              Length@pivots}] /. {f -> Function, p -> Part}], {level}]
     ]

Pivot[data_, heads_, pivots_String, goals_, foo_: Plus] :=
    Block[ {f, p, headerPos = PositionRules@heads,
      level = Length@pivots},
        Map[Rule[#[[1, pivots /. headerPos]],
           foo[#[[All, goals /. headerPos]]]] &,
         GatherBy[SortBy[data, #[[pivots /. headerPos]] &],
          f[p[Slot[1], pivots /. headerPos]] /. {f -> Function,
            p -> Part}]]
    ]


End[];
EndPackage[];