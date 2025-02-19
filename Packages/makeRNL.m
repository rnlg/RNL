(* ::Package:: *)

(*
makeShortcut.m - written by Roman Lee.
*)
PACKAGE="RNL";

SetDirectory[DirectoryName[$InputFileName]]
appdir=$UserBaseDirectory <> "/Applications/"<>PACKAGE<>"/";
files = Join[FileNames["*.wl"],FileNames["*.m"]];
If[files==={},Print["No "<>"*.m, *.wl files in "<>Directory[]<>". Changed nothing, quitting..."];Quit[]];
files=DeleteCases[DeleteDuplicatesBy[files,FileBaseName],FileNameTake[$InputFileName]];
Quiet[CreateDirectory[appdir]];
Scan[Function[file,
fn=appdir<>FileBaseName[file]<>".m";
If[FileExistsQ[fn],write=InputString["You already have "<>fn<>". Overwrite? (y/n)"],write=True];
If[write,
init=OpenWrite[fn];
WriteString[init,"Get[\""<>Directory[]<>"/"<>file<>"\"]"];
Close[init];
Print["Installed shortcut for "<>file<>". Use\n  <<"<>PACKAGE<>"`"<>FileBaseName[file]<>"`"]]],
files]
Quit[]
