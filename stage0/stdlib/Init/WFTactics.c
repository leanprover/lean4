// Lean compiler output
// Module: Init.WFTactics
// Imports: Init.SizeOf Init.MetaTypes Init.WF
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_tacticDecreasing__trivial__pre__omega___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4;
static lean_object* l_tacticSimp__wf___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26;
static lean_object* l_tacticDecreasing__with_____closed__10;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29;
static lean_object* l_tacticDecreasing__tactic___closed__1;
static lean_object* l_tacticClean__wf___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_tacticSimp__wf___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8;
static lean_object* l_tacticDecreasing__with_____closed__8;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36;
static lean_object* l_tacticDecreasing__with_____closed__7;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74;
static lean_object* l_tacticDecreasing__tactic___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32;
static lean_object* l_tacticDecreasing__trivial___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3;
LEAN_EXPORT lean_object* l_tacticDecreasing__trivial__pre__omega;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1;
static lean_object* l_tacticDecreasing__with_____closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24;
static lean_object* l_tacticSimp__wf___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18;
static lean_object* l_tacticDecreasing__trivial___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33;
static lean_object* l_tacticDecreasing__trivial__pre__omega___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8;
LEAN_EXPORT lean_object* l_tacticDecreasing__trivial;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12;
static lean_object* l_tacticSimp__wf___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10;
static lean_object* l_tacticDecreasing__trivial__pre__omega___closed__2;
LEAN_EXPORT lean_object* l_tacticDecreasing__tactic;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
static lean_object* l_tacticDecreasing__trivial___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9;
static lean_object* l_tacticDecreasing__with_____closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66;
static lean_object* l_tacticDecreasing__tactic___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2;
static lean_object* l_tacticDecreasing__with_____closed__9;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21;
LEAN_EXPORT lean_object* l_tacticClean__wf;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28;
static lean_object* l_tacticClean__wf___closed__1;
static lean_object* l_tacticClean__wf___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6;
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
static lean_object* l_tacticClean__wf___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8;
static lean_object* l_tacticDecreasing__trivial__pre__omega___closed__3;
static lean_object* l_tacticDecreasing__with_____closed__6;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22;
static lean_object* l_tacticDecreasing__trivial__pre__omega___closed__4;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80;
lean_object* lean_array_mk(lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30;
static lean_object* l_tacticDecreasing__trivial___closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4;
static lean_object* l_tacticDecreasing__trivial___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15;
static lean_object* l_tacticClean__wf___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72;
static lean_object* l_tacticSimp__wf___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7;
static lean_object* l_tacticDecreasing__with_____closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5;
LEAN_EXPORT lean_object* l_tacticDecreasing__with__;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34;
static lean_object* l_tacticDecreasing__tactic___closed__5;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_tacticDecreasing__with_____closed__5;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6;
static lean_object* l_tacticDecreasing__with_____closed__2;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64;
static lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11;
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
static lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
LEAN_EXPORT lean_object* l_tacticSimp__wf;
static lean_object* l_tacticDecreasing__tactic___closed__3;
static lean_object* _init_l_tacticSimp__wf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSimp_wf", 13, 13);
return x_1;
}
}
static lean_object* _init_l_tacticSimp__wf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticSimp__wf___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticSimp__wf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_wf", 7, 7);
return x_1;
}
}
static lean_object* _init_l_tacticSimp__wf___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticSimp__wf___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticSimp__wf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticSimp__wf___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticSimp__wf___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticSimp__wf() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticSimp__wf___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticTry_", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configItem", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("posConfigItem", 13, 13);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unfoldPartialApp", 16, 16);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zetaDelta", 9, 9);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpLemma", 9, 9);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invImage", 8, 8);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("InvImage", 8, 8);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Prod.lex", 8, 8);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Prod", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lex", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOfWFRel", 11, 11);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("measure", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.lt_wfRel", 12, 12);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_wfRel", 8, 8);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WellFoundedRelation.rel", 23, 23);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WellFoundedRelation", 19, 19);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rel", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticSimp__wf___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21;
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24;
lean_inc(x_11);
lean_inc(x_12);
x_20 = l_Lean_addMacroScope(x_12, x_19, x_11);
x_21 = lean_box(0);
x_22 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23;
lean_inc(x_10);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
lean_inc(x_18);
lean_inc(x_10);
x_25 = l_Lean_Syntax_node2(x_10, x_24, x_18, x_23);
x_26 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_26, x_25);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27;
lean_inc(x_11);
lean_inc(x_12);
x_29 = l_Lean_addMacroScope(x_12, x_28, x_11);
x_30 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26;
lean_inc(x_10);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_21);
lean_inc(x_10);
x_32 = l_Lean_Syntax_node2(x_10, x_24, x_18, x_31);
lean_inc(x_10);
x_33 = l_Lean_Syntax_node1(x_10, x_26, x_32);
x_34 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_35 = l_Lean_Syntax_node2(x_10, x_34, x_27, x_33);
x_36 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
lean_inc(x_10);
x_37 = l_Lean_Syntax_node1(x_10, x_36, x_35);
x_38 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
lean_inc(x_10);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_38);
x_40 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29;
lean_inc(x_10);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34;
lean_inc(x_11);
lean_inc(x_12);
x_43 = l_Lean_addMacroScope(x_12, x_42, x_11);
x_44 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33;
x_45 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36;
lean_inc(x_10);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31;
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_48 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_46);
x_49 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37;
lean_inc(x_10);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40;
lean_inc(x_11);
lean_inc(x_12);
x_52 = l_Lean_addMacroScope(x_12, x_51, x_11);
x_53 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39;
x_54 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44;
lean_inc(x_10);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_56 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_55);
x_57 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49;
lean_inc(x_11);
lean_inc(x_12);
x_58 = l_Lean_addMacroScope(x_12, x_57, x_11);
x_59 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46;
x_60 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53;
lean_inc(x_10);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_62 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_61);
x_63 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56;
lean_inc(x_11);
lean_inc(x_12);
x_64 = l_Lean_addMacroScope(x_12, x_63, x_11);
x_65 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55;
x_66 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58;
lean_inc(x_10);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_10);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_68 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_67);
x_69 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61;
lean_inc(x_11);
lean_inc(x_12);
x_70 = l_Lean_addMacroScope(x_12, x_69, x_11);
x_71 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60;
x_72 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63;
lean_inc(x_10);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_74 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_73);
x_75 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68;
lean_inc(x_11);
lean_inc(x_12);
x_76 = l_Lean_addMacroScope(x_12, x_75, x_11);
x_77 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65;
x_78 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72;
lean_inc(x_10);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_80 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_79);
x_81 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
x_82 = l_Lean_addMacroScope(x_12, x_81, x_11);
x_83 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74;
x_84 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79;
lean_inc(x_10);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_84);
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_86 = l_Lean_Syntax_node3(x_10, x_47, x_39, x_39, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_21);
lean_inc(x_50);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_50);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_50);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_50);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_50);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_50);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_50);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_50);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_62);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_50);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_50);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_56);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_50);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_48);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_mk(x_99);
lean_inc(x_10);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_34);
lean_ctor_set(x_101, 2, x_100);
x_102 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80;
lean_inc(x_10);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_10);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_10);
x_104 = l_Lean_Syntax_node3(x_10, x_34, x_41, x_101, x_103);
x_105 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14;
lean_inc_n(x_39, 2);
lean_inc(x_10);
x_106 = l_Lean_Syntax_node6(x_10, x_105, x_16, x_37, x_39, x_39, x_104, x_39);
lean_inc(x_10);
x_107 = l_Lean_Syntax_node1(x_10, x_34, x_106);
x_108 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10;
lean_inc(x_10);
x_109 = l_Lean_Syntax_node1(x_10, x_108, x_107);
x_110 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8;
lean_inc(x_10);
x_111 = l_Lean_Syntax_node1(x_10, x_110, x_109);
x_112 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5;
x_113 = l_Lean_Syntax_node2(x_10, x_112, x_14, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_3);
return x_114;
}
}
}
static lean_object* _init_l_tacticClean__wf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticClean_wf", 14, 14);
return x_1;
}
}
static lean_object* _init_l_tacticClean__wf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticClean__wf___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticClean__wf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clean_wf", 8, 8);
return x_1;
}
}
static lean_object* _init_l_tacticClean__wf___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticClean__wf___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticClean__wf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticClean__wf___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticClean__wf___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticClean__wf() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticClean__wf___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("negConfigItem", 13, 13);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failIfUnchanged", 15, 15);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOf_nat", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceCtorEq", 12, 12);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticClean__wf___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21;
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24;
lean_inc(x_11);
lean_inc(x_12);
x_18 = l_Lean_addMacroScope(x_12, x_17, x_11);
x_19 = lean_box(0);
x_20 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23;
lean_inc(x_10);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
lean_inc(x_16);
lean_inc(x_10);
x_23 = l_Lean_Syntax_node2(x_10, x_22, x_16, x_21);
x_24 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18;
lean_inc(x_10);
x_25 = l_Lean_Syntax_node1(x_10, x_24, x_23);
x_26 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27;
lean_inc(x_11);
lean_inc(x_12);
x_27 = l_Lean_addMacroScope(x_12, x_26, x_11);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26;
lean_inc(x_10);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_19);
lean_inc(x_10);
x_30 = l_Lean_Syntax_node2(x_10, x_22, x_16, x_29);
lean_inc(x_10);
x_31 = l_Lean_Syntax_node1(x_10, x_24, x_30);
x_32 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3;
lean_inc(x_10);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6;
lean_inc(x_11);
lean_inc(x_12);
x_35 = l_Lean_addMacroScope(x_12, x_34, x_11);
x_36 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5;
lean_inc(x_10);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_19);
x_38 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2;
lean_inc(x_10);
x_39 = l_Lean_Syntax_node2(x_10, x_38, x_33, x_37);
lean_inc(x_10);
x_40 = l_Lean_Syntax_node1(x_10, x_24, x_39);
x_41 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_42 = l_Lean_Syntax_node3(x_10, x_41, x_25, x_31, x_40);
x_43 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
lean_inc(x_10);
x_44 = l_Lean_Syntax_node1(x_10, x_43, x_42);
x_45 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
lean_inc(x_10);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_45);
x_47 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7;
lean_inc(x_10);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_10);
x_49 = l_Lean_Syntax_node1(x_10, x_41, x_48);
x_50 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29;
lean_inc(x_10);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34;
lean_inc(x_11);
lean_inc(x_12);
x_53 = l_Lean_addMacroScope(x_12, x_52, x_11);
x_54 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33;
x_55 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36;
lean_inc(x_10);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_55);
x_57 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31;
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_58 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_56);
x_59 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37;
lean_inc(x_10);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40;
lean_inc(x_11);
lean_inc(x_12);
x_62 = l_Lean_addMacroScope(x_12, x_61, x_11);
x_63 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39;
x_64 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44;
lean_inc(x_10);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_10);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_66 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_65);
x_67 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49;
lean_inc(x_11);
lean_inc(x_12);
x_68 = l_Lean_addMacroScope(x_12, x_67, x_11);
x_69 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46;
x_70 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53;
lean_inc(x_10);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_10);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_70);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_72 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_71);
x_73 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56;
lean_inc(x_11);
lean_inc(x_12);
x_74 = l_Lean_addMacroScope(x_12, x_73, x_11);
x_75 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55;
x_76 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58;
lean_inc(x_10);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_10);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_76);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_78 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_77);
x_79 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61;
lean_inc(x_11);
lean_inc(x_12);
x_80 = l_Lean_addMacroScope(x_12, x_79, x_11);
x_81 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60;
x_82 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63;
lean_inc(x_10);
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_84 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_83);
x_85 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68;
lean_inc(x_11);
lean_inc(x_12);
x_86 = l_Lean_addMacroScope(x_12, x_85, x_11);
x_87 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65;
x_88 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72;
lean_inc(x_10);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_88);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_90 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_89);
x_91 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
lean_inc(x_11);
lean_inc(x_12);
x_92 = l_Lean_addMacroScope(x_12, x_91, x_11);
x_93 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74;
x_94 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79;
lean_inc(x_10);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_10);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_94);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_96 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_95);
x_97 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10;
lean_inc(x_11);
lean_inc(x_12);
x_98 = l_Lean_addMacroScope(x_12, x_97, x_11);
x_99 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9;
x_100 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12;
lean_inc(x_10);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_102 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_101);
x_103 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15;
x_104 = l_Lean_addMacroScope(x_12, x_103, x_11);
x_105 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14;
lean_inc(x_10);
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_10);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
lean_ctor_set(x_106, 3, x_19);
lean_inc_n(x_46, 2);
lean_inc(x_10);
x_107 = l_Lean_Syntax_node3(x_10, x_57, x_46, x_46, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_19);
lean_inc(x_60);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_60);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_102);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_60);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_60);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_96);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_60);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_60);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_90);
lean_ctor_set(x_114, 1, x_113);
lean_inc(x_60);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_60);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_84);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_60);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_60);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_78);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_60);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_60);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_72);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_60);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_60);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_66);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_60);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_58);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_mk(x_124);
lean_inc(x_10);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_10);
lean_ctor_set(x_126, 1, x_41);
lean_ctor_set(x_126, 2, x_125);
x_127 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80;
lean_inc(x_10);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_10);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_10);
x_129 = l_Lean_Syntax_node3(x_10, x_41, x_51, x_126, x_128);
x_130 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14;
lean_inc(x_46);
x_131 = l_Lean_Syntax_node6(x_10, x_130, x_14, x_44, x_46, x_49, x_129, x_46);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_3);
return x_132;
}
}
}
static lean_object* _init_l_tacticDecreasing__trivial___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticDecreasing_trivial", 24, 24);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__trivial___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticDecreasing__trivial___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__trivial___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decreasing_trivial", 18, 18);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__trivial___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticDecreasing__trivial___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__trivial___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticDecreasing__trivial___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticDecreasing__trivial___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__trivial() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticDecreasing__trivial___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<;>", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("done", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21;
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8;
lean_inc(x_11);
lean_inc(x_12);
x_20 = l_Lean_addMacroScope(x_12, x_19, x_11);
x_21 = lean_box(0);
x_22 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7;
lean_inc(x_10);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
lean_inc(x_10);
x_25 = l_Lean_Syntax_node2(x_10, x_24, x_18, x_23);
x_26 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_26, x_25);
x_28 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3;
lean_inc(x_10);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6;
x_31 = l_Lean_addMacroScope(x_12, x_30, x_11);
x_32 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5;
lean_inc(x_10);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_21);
x_34 = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2;
lean_inc(x_10);
x_35 = l_Lean_Syntax_node2(x_10, x_34, x_29, x_33);
lean_inc(x_10);
x_36 = l_Lean_Syntax_node1(x_10, x_26, x_35);
x_37 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_38 = l_Lean_Syntax_node2(x_10, x_37, x_27, x_36);
x_39 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
lean_inc(x_10);
x_40 = l_Lean_Syntax_node1(x_10, x_39, x_38);
x_41 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
lean_inc(x_10);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_41);
x_43 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14;
lean_inc_n(x_42, 3);
lean_inc(x_10);
x_44 = l_Lean_Syntax_node6(x_10, x_43, x_16, x_40, x_42, x_42, x_42, x_42);
lean_inc(x_10);
x_45 = l_Lean_Syntax_node1(x_10, x_37, x_44);
x_46 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10;
lean_inc(x_10);
x_47 = l_Lean_Syntax_node1(x_10, x_46, x_45);
x_48 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8;
lean_inc(x_10);
x_49 = l_Lean_Syntax_node1(x_10, x_48, x_47);
x_50 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9;
lean_inc(x_10);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4;
lean_inc(x_10);
x_53 = l_Lean_Syntax_node3(x_10, x_52, x_14, x_49, x_51);
x_54 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10;
lean_inc(x_10);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
lean_inc(x_10);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12;
lean_inc(x_10);
x_59 = l_Lean_Syntax_node1(x_10, x_58, x_57);
x_60 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2;
x_61 = l_Lean_Syntax_node3(x_10, x_60, x_53, x_55, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
x_14 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
lean_inc(x_10);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
lean_inc(x_10);
x_17 = l_Lean_Syntax_node1(x_10, x_16, x_15);
x_18 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2;
x_19 = l_Lean_Syntax_node2(x_10, x_18, x_12, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assumption", 10, 10);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2;
x_14 = l_Lean_Syntax_node1(x_10, x_13, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticDecreasing_trivial_pre_omega", 34, 34);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticDecreasing__trivial__pre__omega___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decreasing_trivial_pre_omega", 28, 28);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticDecreasing__trivial__pre__omega___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticDecreasing__trivial__pre__omega___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticDecreasing__trivial__pre__omega___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__trivial__pre__omega() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticDecreasing__trivial__pre__omega___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seq1", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("apply", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.sub_succ_lt_self", 20, 20);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sub_succ_lt_self", 16, 16);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial__pre__omega___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8;
x_16 = l_Lean_addMacroScope(x_12, x_15, x_11);
x_17 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6;
x_18 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
lean_inc(x_10);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
lean_inc(x_10);
x_21 = l_Lean_Syntax_node2(x_10, x_20, x_14, x_19);
x_22 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11;
lean_inc(x_10);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
lean_inc(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_26, x_25);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_29 = l_Lean_Syntax_node3(x_10, x_28, x_21, x_23, x_27);
x_30 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
x_31 = l_Lean_Syntax_node1(x_10, x_30, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.pred_lt_of_lt", 17, 17);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pred_lt_of_lt", 13, 13);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial__pre__omega___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4;
x_16 = l_Lean_addMacroScope(x_12, x_15, x_11);
x_17 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2;
x_18 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6;
lean_inc(x_10);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
lean_inc(x_10);
x_21 = l_Lean_Syntax_node2(x_10, x_20, x_14, x_19);
x_22 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11;
lean_inc(x_10);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
lean_inc(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_26, x_25);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_29 = l_Lean_Syntax_node3(x_10, x_28, x_21, x_23, x_27);
x_30 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
x_31 = l_Lean_Syntax_node1(x_10, x_30, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.pred_lt", 11, 11);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pred_lt", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__trivial__pre__omega___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4;
x_16 = l_Lean_addMacroScope(x_12, x_15, x_11);
x_17 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2;
x_18 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6;
lean_inc(x_10);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
lean_inc(x_10);
x_21 = l_Lean_Syntax_node2(x_10, x_20, x_14, x_19);
x_22 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11;
lean_inc(x_10);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
lean_inc(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2;
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_26, x_25);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_10);
x_29 = l_Lean_Syntax_node3(x_10, x_28, x_21, x_23, x_27);
x_30 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
x_31 = l_Lean_Syntax_node1(x_10, x_30, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticDecreasing_with_", 22, 22);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticDecreasing__with_____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticDecreasing__with_____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decreasing_with ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticDecreasing__with_____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_tacticDecreasing__with_____closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticDecreasing__with_____closed__4;
x_2 = l_tacticDecreasing__with_____closed__6;
x_3 = l_tacticDecreasing__with_____closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__with_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticDecreasing__with_____closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_tacticDecreasing__with_____closed__9;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__with__() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticDecreasing__with_____closed__10;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticRepeat_", 13, 13);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("repeat", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("first", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("|", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Prod.Lex.right", 14, 14);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lex", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("right", 5, 5);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11;
x_3 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Prod.Lex.left", 13, 13);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("left", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11;
x_3 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PSigma.Lex.right", 16, 16);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PSigma", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11;
x_3 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PSigma.Lex.left", 15, 15);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24;
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11;
x_3 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fail", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"failed to prove termination, possible solutions:\n  - Use `have`-expressions to prove the remaining goals\n  - Use `termination_by` to specify a different well-founded relation\n  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal\"", 261, 261);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__with_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_tacticClean__wf___closed__3;
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_tacticClean__wf___closed__2;
lean_inc(x_12);
x_20 = l_Lean_Syntax_node1(x_12, x_19, x_18);
x_21 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
x_22 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
lean_inc(x_12);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6;
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16;
lean_inc(x_23);
lean_inc(x_12);
x_29 = l_Lean_Syntax_node1(x_12, x_28, x_23);
x_30 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14;
lean_inc_n(x_23, 4);
lean_inc(x_12);
x_31 = l_Lean_Syntax_node6(x_12, x_30, x_27, x_29, x_23, x_23, x_23, x_23);
lean_inc(x_12);
x_32 = l_Lean_Syntax_node1(x_12, x_21, x_31);
x_33 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10;
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_33, x_32);
x_35 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8;
lean_inc(x_12);
x_36 = l_Lean_Syntax_node1(x_12, x_35, x_34);
x_37 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5;
lean_inc(x_12);
x_38 = l_Lean_Syntax_node2(x_12, x_37, x_25, x_36);
x_39 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3;
lean_inc(x_12);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
lean_inc(x_12);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8;
lean_inc(x_12);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
lean_inc(x_12);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13;
lean_inc(x_13);
lean_inc(x_14);
x_48 = l_Lean_addMacroScope(x_14, x_47, x_13);
x_49 = lean_box(0);
x_50 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10;
x_51 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15;
lean_inc(x_12);
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_51);
x_53 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
lean_inc(x_46);
lean_inc(x_12);
x_54 = l_Lean_Syntax_node2(x_12, x_53, x_46, x_52);
lean_inc(x_12);
x_55 = l_Lean_Syntax_node1(x_12, x_21, x_54);
lean_inc(x_12);
x_56 = l_Lean_Syntax_node1(x_12, x_33, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node1(x_12, x_35, x_56);
x_58 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7;
lean_inc(x_44);
lean_inc(x_12);
x_59 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_57);
x_60 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19;
lean_inc(x_13);
lean_inc(x_14);
x_61 = l_Lean_addMacroScope(x_14, x_60, x_13);
x_62 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17;
x_63 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21;
lean_inc(x_12);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_63);
lean_inc(x_46);
lean_inc(x_12);
x_65 = l_Lean_Syntax_node2(x_12, x_53, x_46, x_64);
lean_inc(x_12);
x_66 = l_Lean_Syntax_node1(x_12, x_21, x_65);
lean_inc(x_12);
x_67 = l_Lean_Syntax_node1(x_12, x_33, x_66);
lean_inc(x_12);
x_68 = l_Lean_Syntax_node1(x_12, x_35, x_67);
lean_inc(x_44);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_68);
lean_inc(x_12);
x_70 = l_Lean_Syntax_node2(x_12, x_21, x_59, x_69);
x_71 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5;
lean_inc(x_42);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node2(x_12, x_71, x_42, x_70);
lean_inc(x_12);
x_73 = l_Lean_Syntax_node1(x_12, x_21, x_72);
lean_inc(x_12);
x_74 = l_Lean_Syntax_node1(x_12, x_33, x_73);
lean_inc(x_12);
x_75 = l_Lean_Syntax_node1(x_12, x_35, x_74);
x_76 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9;
lean_inc(x_12);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4;
lean_inc(x_77);
lean_inc(x_16);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node3(x_12, x_78, x_16, x_75, x_77);
lean_inc(x_12);
x_80 = l_Lean_Syntax_node1(x_12, x_21, x_79);
lean_inc(x_12);
x_81 = l_Lean_Syntax_node1(x_12, x_33, x_80);
lean_inc(x_12);
x_82 = l_Lean_Syntax_node1(x_12, x_35, x_81);
x_83 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2;
lean_inc(x_40);
lean_inc(x_12);
x_84 = l_Lean_Syntax_node2(x_12, x_83, x_40, x_82);
x_85 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25;
lean_inc(x_13);
lean_inc(x_14);
x_86 = l_Lean_addMacroScope(x_14, x_85, x_13);
x_87 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23;
x_88 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27;
lean_inc(x_12);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_12);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_88);
lean_inc(x_46);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node2(x_12, x_53, x_46, x_89);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node1(x_12, x_21, x_90);
lean_inc(x_12);
x_92 = l_Lean_Syntax_node1(x_12, x_33, x_91);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node1(x_12, x_35, x_92);
lean_inc(x_44);
lean_inc(x_12);
x_94 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_93);
x_95 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30;
x_96 = l_Lean_addMacroScope(x_14, x_95, x_13);
x_97 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29;
x_98 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32;
lean_inc(x_12);
x_99 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_99, 0, x_12);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_98);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node2(x_12, x_53, x_46, x_99);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node1(x_12, x_21, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node1(x_12, x_33, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node1(x_12, x_35, x_102);
lean_inc(x_44);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_103);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node2(x_12, x_21, x_94, x_104);
lean_inc(x_42);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node2(x_12, x_71, x_42, x_105);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node1(x_12, x_21, x_106);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node1(x_12, x_33, x_107);
lean_inc(x_12);
x_109 = l_Lean_Syntax_node1(x_12, x_35, x_108);
lean_inc(x_77);
lean_inc(x_16);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node3(x_12, x_78, x_16, x_109, x_77);
lean_inc(x_12);
x_111 = l_Lean_Syntax_node1(x_12, x_21, x_110);
lean_inc(x_12);
x_112 = l_Lean_Syntax_node1(x_12, x_33, x_111);
lean_inc(x_12);
x_113 = l_Lean_Syntax_node1(x_12, x_35, x_112);
lean_inc(x_12);
x_114 = l_Lean_Syntax_node2(x_12, x_83, x_40, x_113);
x_115 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
lean_inc(x_12);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_12);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12;
lean_inc(x_12);
x_118 = l_Lean_Syntax_node1(x_12, x_117, x_116);
lean_inc(x_12);
x_119 = l_Lean_Syntax_node1(x_12, x_21, x_118);
lean_inc(x_12);
x_120 = l_Lean_Syntax_node1(x_12, x_33, x_119);
lean_inc(x_12);
x_121 = l_Lean_Syntax_node1(x_12, x_35, x_120);
lean_inc(x_44);
lean_inc(x_12);
x_122 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_121);
lean_inc(x_44);
lean_inc(x_12);
x_123 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_9);
x_124 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33;
lean_inc(x_12);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_12);
lean_ctor_set(x_125, 1, x_124);
x_126 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37;
lean_inc(x_12);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_12);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36;
lean_inc(x_12);
x_129 = l_Lean_Syntax_node1(x_12, x_128, x_127);
lean_inc(x_12);
x_130 = l_Lean_Syntax_node1(x_12, x_21, x_129);
x_131 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34;
lean_inc(x_12);
x_132 = l_Lean_Syntax_node2(x_12, x_131, x_125, x_130);
lean_inc(x_12);
x_133 = l_Lean_Syntax_node1(x_12, x_21, x_132);
lean_inc(x_12);
x_134 = l_Lean_Syntax_node1(x_12, x_33, x_133);
lean_inc(x_12);
x_135 = l_Lean_Syntax_node1(x_12, x_35, x_134);
lean_inc(x_12);
x_136 = l_Lean_Syntax_node2(x_12, x_58, x_44, x_135);
lean_inc(x_12);
x_137 = l_Lean_Syntax_node3(x_12, x_21, x_122, x_123, x_136);
lean_inc(x_12);
x_138 = l_Lean_Syntax_node2(x_12, x_71, x_42, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_49);
lean_inc(x_23);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_23);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_114);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_23);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_23);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_84);
lean_ctor_set(x_143, 1, x_142);
lean_inc(x_23);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_23);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_38);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_23);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_20);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_mk(x_147);
lean_inc(x_12);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_12);
lean_ctor_set(x_149, 1, x_21);
lean_ctor_set(x_149, 2, x_148);
lean_inc(x_12);
x_150 = l_Lean_Syntax_node1(x_12, x_33, x_149);
lean_inc(x_12);
x_151 = l_Lean_Syntax_node1(x_12, x_35, x_150);
x_152 = l_Lean_Syntax_node3(x_12, x_78, x_16, x_151, x_77);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
return x_153;
}
}
}
static lean_object* _init_l_tacticDecreasing__tactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticDecreasing_tactic", 23, 23);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__tactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_tacticDecreasing__tactic___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__tactic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decreasing_tactic", 17, 17);
return x_1;
}
}
static lean_object* _init_l_tacticDecreasing__tactic___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_tacticDecreasing__tactic___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_tacticDecreasing__tactic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_tacticDecreasing__tactic___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_tacticDecreasing__tactic___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_tacticDecreasing__tactic() {
_start:
{
lean_object* x_1; 
x_1 = l_tacticDecreasing__tactic___closed__5;
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decreasing_with", 15, 15);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("substVars", 9, 9);
return x_1;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1;
x_2 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2;
x_3 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3;
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst_vars", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_tacticDecreasing__tactic___closed__2;
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
lean_inc(x_10);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8;
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_tacticDecreasing__trivial___closed__3;
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_tacticDecreasing__trivial___closed__2;
lean_inc(x_10);
x_20 = l_Lean_Syntax_node1(x_10, x_19, x_18);
x_21 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
lean_inc(x_20);
lean_inc(x_10);
x_22 = l_Lean_Syntax_node1(x_10, x_21, x_20);
x_23 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10;
lean_inc(x_10);
x_24 = l_Lean_Syntax_node1(x_10, x_23, x_22);
x_25 = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8;
lean_inc(x_10);
x_26 = l_Lean_Syntax_node1(x_10, x_25, x_24);
x_27 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7;
lean_inc(x_16);
lean_inc(x_10);
x_28 = l_Lean_Syntax_node2(x_10, x_27, x_16, x_26);
x_29 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4;
lean_inc(x_10);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3;
lean_inc(x_10);
x_32 = l_Lean_Syntax_node1(x_10, x_31, x_30);
x_33 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11;
lean_inc(x_10);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_10);
x_35 = l_Lean_Syntax_node3(x_10, x_21, x_32, x_34, x_20);
lean_inc(x_10);
x_36 = l_Lean_Syntax_node1(x_10, x_23, x_35);
lean_inc(x_10);
x_37 = l_Lean_Syntax_node1(x_10, x_25, x_36);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node2(x_10, x_27, x_16, x_37);
lean_inc(x_10);
x_39 = l_Lean_Syntax_node2(x_10, x_21, x_28, x_38);
x_40 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5;
lean_inc(x_10);
x_41 = l_Lean_Syntax_node2(x_10, x_40, x_14, x_39);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node1(x_10, x_21, x_41);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node1(x_10, x_23, x_42);
lean_inc(x_10);
x_44 = l_Lean_Syntax_node1(x_10, x_25, x_43);
x_45 = l_tacticDecreasing__with_____closed__2;
x_46 = l_Lean_Syntax_node2(x_10, x_45, x_12, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_SizeOf(uint8_t builtin, lean_object*);
lean_object* initialize_Init_MetaTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_WFTactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_SizeOf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_tacticSimp__wf___closed__1 = _init_l_tacticSimp__wf___closed__1();
lean_mark_persistent(l_tacticSimp__wf___closed__1);
l_tacticSimp__wf___closed__2 = _init_l_tacticSimp__wf___closed__2();
lean_mark_persistent(l_tacticSimp__wf___closed__2);
l_tacticSimp__wf___closed__3 = _init_l_tacticSimp__wf___closed__3();
lean_mark_persistent(l_tacticSimp__wf___closed__3);
l_tacticSimp__wf___closed__4 = _init_l_tacticSimp__wf___closed__4();
lean_mark_persistent(l_tacticSimp__wf___closed__4);
l_tacticSimp__wf___closed__5 = _init_l_tacticSimp__wf___closed__5();
lean_mark_persistent(l_tacticSimp__wf___closed__5);
l_tacticSimp__wf = _init_l_tacticSimp__wf();
lean_mark_persistent(l_tacticSimp__wf);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__78);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__79);
l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80 = _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__80);
l_tacticClean__wf___closed__1 = _init_l_tacticClean__wf___closed__1();
lean_mark_persistent(l_tacticClean__wf___closed__1);
l_tacticClean__wf___closed__2 = _init_l_tacticClean__wf___closed__2();
lean_mark_persistent(l_tacticClean__wf___closed__2);
l_tacticClean__wf___closed__3 = _init_l_tacticClean__wf___closed__3();
lean_mark_persistent(l_tacticClean__wf___closed__3);
l_tacticClean__wf___closed__4 = _init_l_tacticClean__wf___closed__4();
lean_mark_persistent(l_tacticClean__wf___closed__4);
l_tacticClean__wf___closed__5 = _init_l_tacticClean__wf___closed__5();
lean_mark_persistent(l_tacticClean__wf___closed__5);
l_tacticClean__wf = _init_l_tacticClean__wf();
lean_mark_persistent(l_tacticClean__wf);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14);
l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15 = _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__15);
l_tacticDecreasing__trivial___closed__1 = _init_l_tacticDecreasing__trivial___closed__1();
lean_mark_persistent(l_tacticDecreasing__trivial___closed__1);
l_tacticDecreasing__trivial___closed__2 = _init_l_tacticDecreasing__trivial___closed__2();
lean_mark_persistent(l_tacticDecreasing__trivial___closed__2);
l_tacticDecreasing__trivial___closed__3 = _init_l_tacticDecreasing__trivial___closed__3();
lean_mark_persistent(l_tacticDecreasing__trivial___closed__3);
l_tacticDecreasing__trivial___closed__4 = _init_l_tacticDecreasing__trivial___closed__4();
lean_mark_persistent(l_tacticDecreasing__trivial___closed__4);
l_tacticDecreasing__trivial___closed__5 = _init_l_tacticDecreasing__trivial___closed__5();
lean_mark_persistent(l_tacticDecreasing__trivial___closed__5);
l_tacticDecreasing__trivial = _init_l_tacticDecreasing__trivial();
lean_mark_persistent(l_tacticDecreasing__trivial);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__12);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__2);
l_tacticDecreasing__trivial__pre__omega___closed__1 = _init_l_tacticDecreasing__trivial__pre__omega___closed__1();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega___closed__1);
l_tacticDecreasing__trivial__pre__omega___closed__2 = _init_l_tacticDecreasing__trivial__pre__omega___closed__2();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega___closed__2);
l_tacticDecreasing__trivial__pre__omega___closed__3 = _init_l_tacticDecreasing__trivial__pre__omega___closed__3();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega___closed__3);
l_tacticDecreasing__trivial__pre__omega___closed__4 = _init_l_tacticDecreasing__trivial__pre__omega___closed__4();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega___closed__4);
l_tacticDecreasing__trivial__pre__omega___closed__5 = _init_l_tacticDecreasing__trivial__pre__omega___closed__5();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega___closed__5);
l_tacticDecreasing__trivial__pre__omega = _init_l_tacticDecreasing__trivial__pre__omega();
lean_mark_persistent(l_tacticDecreasing__trivial__pre__omega);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__11);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__6);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__6);
l_tacticDecreasing__with_____closed__1 = _init_l_tacticDecreasing__with_____closed__1();
lean_mark_persistent(l_tacticDecreasing__with_____closed__1);
l_tacticDecreasing__with_____closed__2 = _init_l_tacticDecreasing__with_____closed__2();
lean_mark_persistent(l_tacticDecreasing__with_____closed__2);
l_tacticDecreasing__with_____closed__3 = _init_l_tacticDecreasing__with_____closed__3();
lean_mark_persistent(l_tacticDecreasing__with_____closed__3);
l_tacticDecreasing__with_____closed__4 = _init_l_tacticDecreasing__with_____closed__4();
lean_mark_persistent(l_tacticDecreasing__with_____closed__4);
l_tacticDecreasing__with_____closed__5 = _init_l_tacticDecreasing__with_____closed__5();
lean_mark_persistent(l_tacticDecreasing__with_____closed__5);
l_tacticDecreasing__with_____closed__6 = _init_l_tacticDecreasing__with_____closed__6();
lean_mark_persistent(l_tacticDecreasing__with_____closed__6);
l_tacticDecreasing__with_____closed__7 = _init_l_tacticDecreasing__with_____closed__7();
lean_mark_persistent(l_tacticDecreasing__with_____closed__7);
l_tacticDecreasing__with_____closed__8 = _init_l_tacticDecreasing__with_____closed__8();
lean_mark_persistent(l_tacticDecreasing__with_____closed__8);
l_tacticDecreasing__with_____closed__9 = _init_l_tacticDecreasing__with_____closed__9();
lean_mark_persistent(l_tacticDecreasing__with_____closed__9);
l_tacticDecreasing__with_____closed__10 = _init_l_tacticDecreasing__with_____closed__10();
lean_mark_persistent(l_tacticDecreasing__with_____closed__10);
l_tacticDecreasing__with__ = _init_l_tacticDecreasing__with__();
lean_mark_persistent(l_tacticDecreasing__with__);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__37);
l_tacticDecreasing__tactic___closed__1 = _init_l_tacticDecreasing__tactic___closed__1();
lean_mark_persistent(l_tacticDecreasing__tactic___closed__1);
l_tacticDecreasing__tactic___closed__2 = _init_l_tacticDecreasing__tactic___closed__2();
lean_mark_persistent(l_tacticDecreasing__tactic___closed__2);
l_tacticDecreasing__tactic___closed__3 = _init_l_tacticDecreasing__tactic___closed__3();
lean_mark_persistent(l_tacticDecreasing__tactic___closed__3);
l_tacticDecreasing__tactic___closed__4 = _init_l_tacticDecreasing__tactic___closed__4();
lean_mark_persistent(l_tacticDecreasing__tactic___closed__4);
l_tacticDecreasing__tactic___closed__5 = _init_l_tacticDecreasing__tactic___closed__5();
lean_mark_persistent(l_tacticDecreasing__tactic___closed__5);
l_tacticDecreasing__tactic = _init_l_tacticDecreasing__tactic();
lean_mark_persistent(l_tacticDecreasing__tactic);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3);
l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4 = _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4();
lean_mark_persistent(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
