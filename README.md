# `lake exe ast-export` command

This command will export the AST of a lean file or project.

For example, the following lean file `Test.lean`:
```lean
import Lean

def foo := 2 + 2

#eval foo

example : foo = 4 := by decide
```

can be translated using `lake exe ast-export --one Test`, producing `.lake/build/lib/Test.out.json`:
```json
{"header":
 {"kind": "Lean.Parser.Module.header",
  "info": null,
  "args":
  [[],
   [{"kind": "Lean.Parser.Module.import",
     "info": null,
     "args":
     [{"val": "import",
       "info": {"trailing": " ", "pos": [0, 6], "leading": ""}},
      [],
      {"val": "Lean",
       "rawVal": "Lean",
       "info": {"trailing": "\n\n", "pos": [7, 11], "leading": ""}},
      []]}]]},
 "commands":
 [{"kind": "Lean.Parser.Command.declaration",
   "info": null,
   "args":
   [{"kind": "Lean.Parser.Command.declModifiers",
     "info": null,
     "args": [[], [], [], [], [], []]},
    {"kind": "Lean.Parser.Command.definition",
     "info": null,
     "args":
     [{"val": "def", "info": {"trailing": " ", "pos": [13, 16], "leading": ""}},
      {"kind": "Lean.Parser.Command.declId",
       "info": null,
       "args":
       [{"val": "foo",
         "rawVal": "foo",
         "info": {"trailing": " ", "pos": [17, 20], "leading": ""}},
        []]},
      {"kind": "Lean.Parser.Command.optDeclSig",
       "info": null,
       "args": [[], []]},
      {"kind": "Lean.Parser.Command.declValSimple",
       "info": null,
       "args":
       [{"val": ":=",
         "info": {"trailing": " ", "pos": [21, 23], "leading": ""}},
        {"kind": "Lean.Parser.Term.tuple",
         "info": null,
         "args":
         [{"val": "(",
           "info": {"trailing": "", "pos": [24, 25], "leading": ""}},
          [{"kind": "«term_+_»",
            "info": null,
            "args":
            [{"kind": "num",
              "info": null,
              "args":
              [{"val": "2",
                "info": {"trailing": " ", "pos": [25, 26], "leading": ""}}]},
             {"val": "+",
              "info": {"trailing": " ", "pos": [27, 28], "leading": ""}},
             {"kind": "num",
              "info": null,
              "args":
              [{"val": "2",
                "info": {"trailing": "", "pos": [29, 30], "leading": ""}}]}]},
           {"val": ",",
            "info": {"trailing": " ", "pos": [30, 31], "leading": ""}},
           [{"kind": "num",
             "info": null,
             "args":
             [{"val": "1",
               "info": {"trailing": "", "pos": [32, 33], "leading": ""}}]}]],
          {"val": ")",
           "info": {"trailing": "\n\n", "pos": [33, 34], "leading": ""}}]},
        {"kind": "Lean.Parser.Termination.suffix",
         "info": null,
         "args": [[], []]},
        []]},
      []]}]},
  {"kind": "Lean.Parser.Command.eval",
   "info": null,
   "args":
   [{"val": "#eval", "info": {"trailing": " ", "pos": [36, 41], "leading": ""}},
    {"val": "foo",
     "rawVal": "foo",
     "info": {"trailing": "\n\n", "pos": [42, 45], "leading": ""}}]},
  {"kind": "Lean.Parser.Command.declaration",
   "info": null,
   "args":
   [{"kind": "Lean.Parser.Command.declModifiers",
     "info": null,
     "args": [[], [], [], [], [], []]},
    {"kind": "Lean.Parser.Command.example",
     "info": null,
     "args":
     [{"val": "example",
       "info": {"trailing": " ", "pos": [47, 54], "leading": ""}},
      {"kind": "Lean.Parser.Command.optDeclSig",
       "info": null,
       "args":
       [[],
        [{"kind": "Lean.Parser.Term.typeSpec",
          "info": null,
          "args":
          [{"val": ":",
            "info": {"trailing": " ", "pos": [55, 56], "leading": ""}},
           {"kind": "«term_=_»",
            "info": null,
            "args":
            [{"kind": "Lean.Parser.Term.proj",
              "info": null,
              "args":
              [{"val": "foo",
                "rawVal": "foo",
                "info": {"trailing": "", "pos": [57, 60], "leading": ""}},
               {"val": ".",
                "info": {"trailing": "", "pos": [60, 61], "leading": ""}},
               {"kind": "fieldIdx",
                "info": null,
                "args":
                [{"val": "1",
                  "info":
                  {"trailing": " ", "pos": [61, 62], "leading": ""}}]}]},
             {"val": "=",
              "info": {"trailing": " ", "pos": [63, 64], "leading": ""}},
             {"kind": "num",
              "info": null,
              "args":
              [{"val": "4",
                "info":
                {"trailing": " ", "pos": [65, 66], "leading": ""}}]}]}]}]]},
      {"kind": "Lean.Parser.Command.declValSimple",
       "info": null,
       "args":
       [{"val": ":=",
         "info": {"trailing": " ", "pos": [67, 69], "leading": ""}},
        {"kind": "Lean.Parser.Term.byTactic",
         "info": null,
         "args":
         [{"val": "by",
           "info": {"trailing": " ", "pos": [70, 72], "leading": ""}},
          {"kind": "Lean.Parser.Tactic.tacticSeq",
           "info": null,
           "args":
           [{"kind": "Lean.Parser.Tactic.tacticSeq1Indented",
             "info": null,
             "args":
             [[{"kind": "Lean.Parser.Tactic.decide",
                "info": null,
                "args":
                [{"val": "decide",
                  "info":
                  {"trailing": "\n", "pos": [73, 79], "leading": ""}}]}]]}]}]},
        {"kind": "Lean.Parser.Termination.suffix",
         "info": null,
         "args": [[], []]},
        []]}]}]}]}
```

