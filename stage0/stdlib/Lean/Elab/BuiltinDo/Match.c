// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Match
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar import Lean.Elab.BuiltinDo.Basic import Lean.Elab.Match import Lean.Elab.MatchAltView import Lean.Data.Array import Init.Omega
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "Could not determine dependently-refined result type of `do` block.\n\n        Expected type "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " was not def eq to "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3;
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 179, 20, 242, 208, 252, 205, 79)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 70, 204, 102, 119, 217, 163, 216)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "newDoBlockResultType: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5;
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__4_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__7_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__9_value),LEAN_SCALAR_PTR_LITERAL(81, 58, 182, 248, 224, 44, 170, 90)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__15_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "generalizing"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__17_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__18_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "match_syntax alternative "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__20 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Do_getPatternsVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntaxWithExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "Dependent match is not supported when the result type of the `do` block "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\n is different to the result type of the `match` "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ", doBlockResultType: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", dec.resultType: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__8_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "expandToTermMatch. dependent: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__12_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trueVal"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__14_value),LEAN_SCALAR_PTR_LITERAL(67, 57, 186, 163, 64, 69, 53, 80)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__16_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17_value;
lean_object* l_Lean_Elab_Do_DoElemCont_withDuplicableCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_isAtomicDiscr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabNonAtomicDiscrs: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "discr "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__2_value;
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPatternElabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0;
lean_object* l_Lean_Elab_Term_checkNumPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_withElaboratedLHS_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__1_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2;
static const lean_string_object l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "patterns: "};
static const lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4;
lean_object* l_Lean_Elab_Term_ToDepElimPattern_main___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalInstancesImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rhs: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabMatchAlt: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3;
lean_object* lean_array_mk(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternVars: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1;
lean_object* l_Lean_Elab_Term_collectPatternVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPatternVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1;
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__21_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doSeq"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 92, 223, 18, 180, 209, 3, 4)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__2_value;
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "result: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3;
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportMatcherResultErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateAltLHSs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "discrs: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = ", nondupDec.resultType: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ", may postpone: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5;
lean_object* l_Lean_Elab_Term_commitIfDidNotPostpone___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_ControlInfo_pure;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "namedPattern"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 38, 53, 234, 94, 148, 183, 69)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0(lean_object*, size_t, size_t);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Do_isSyntaxMatch(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isSyntaxMatch___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getAltsPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getAltsPatternVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_getMatchAlt___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "The `do` elaborator does not support dependent matches and generalization by default. Try `(dependent := true)`."};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoMatch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoMatch___closed__1;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 191, .m_capacity = 191, .m_length = 190, .m_data = "The `do` elaborator does not support custom motives.\nIf you want a dependent match, try `(dependent := true)`.\nIf you want to provide an expected type, do so via type ascription on the bind."};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoMatch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoMatch___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__4_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__8_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__13_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__15_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__18_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__20_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___closed__21_value;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isPatternVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabDoMatch"};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 228, 9, 9, 140, 39, 228, 140)}};
static const lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2_value;
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(x_1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_Lean_Level_succ___override(x_11);
x_13 = l_Lean_mkSort(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = 0;
x_16 = lean_box(0);
lean_inc_ref(x_5);
x_17 = l_Lean_Meta_mkFreshExprMVar(x_14, x_15, x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_2);
lean_inc(x_18);
x_19 = l_Lean_Elab_Do_mkMonadicType___redArg(x_18, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_21 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_20, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Elab_Do_mkMonadicType___redArg(x_18, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__1);
x_27 = l_Lean_MessageData_ofExpr(x_1);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___closed__3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofExpr(x_25);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_32, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_24;
}
}
else
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(x_18, x_6);
lean_dec(x_6);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___lam__0___boxed), 9, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__2___redArg(x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_52 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_53 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_52, x_9);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__5);
lean_inc(x_15);
x_57 = l_Lean_MessageData_ofExpr(x_15);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_52, x_58, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = lean_box(0);
goto block_51;
}
else
{
uint8_t x_60; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_51:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 3);
lean_dec(x_27);
lean_inc(x_15);
lean_ctor_set(x_3, 1, x_15);
x_28 = 1;
lean_ctor_set(x_16, 3, x_15);
x_29 = l_Lean_Elab_Do_elabDoSeq(x_2, x_3, x_28, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 4);
x_34 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
lean_inc(x_15);
lean_ctor_set(x_3, 1, x_15);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_15);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_34);
x_37 = l_Lean_Elab_Do_elabDoSeq(x_2, x_3, x_35, x_36, x_17, x_18, x_19, x_20, x_21, x_22);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_41 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_16, 4);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_16, sizeof(void*)*5);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_46 = x_16;
} else {
 lean_dec_ref(x_16);
 x_46 = lean_box(0);
}
lean_inc(x_15);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_40);
x_48 = 1;
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 5, 1);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_15);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_45);
x_50 = l_Lean_Elab_Do_elabDoSeq(x_2, x_47, x_48, x_49, x_17, x_18, x_19, x_20, x_21, x_22);
return x_50;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofSyntax(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofSyntax(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 1)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec_ref(x_5);
x_15 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType(x_14, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = l_Lean_Elab_Do_elabDoSeq(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = l_Lean_Elab_Do_elabDoSeq(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_4);
x_16 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1(x_14, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__4));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_10);
x_22 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__20));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_8);
x_18 = lean_nat_dec_lt(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_49; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_19 = lean_ctor_get(x_14, 5);
x_20 = l_Lean_SourceInfo_fromRef(x_19, x_18);
x_21 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2));
x_22 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__3));
lean_inc(x_20);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_24 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2));
x_25 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec_ref(x_1);
x_67 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16));
x_68 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11));
lean_inc(x_20);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_20);
lean_ctor_set(x_69, 1, x_68);
x_70 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__17));
lean_inc(x_20);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_20);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12));
lean_inc(x_20);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_20);
lean_ctor_set(x_73, 1, x_72);
x_74 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13));
lean_inc(x_20);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_20);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_20);
x_76 = l_Lean_Syntax_node5(x_20, x_67, x_69, x_71, x_73, x_66, x_75);
x_77 = l_Array_mkArray1___redArg(x_76);
x_49 = x_77;
goto block_65;
}
else
{
lean_object* x_78; 
lean_dec(x_1);
x_78 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_49 = x_78;
goto block_65;
}
block_48:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_28 = l_Array_append___redArg(x_25, x_27);
lean_dec_ref(x_27);
lean_inc(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec_ref(x_3);
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__0(x_31, x_32, x_30);
x_34 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__5);
x_35 = l_Lean_mkSepArray(x_33, x_34);
lean_dec_ref(x_33);
x_36 = l_Array_append___redArg(x_25, x_35);
lean_dec_ref(x_35);
lean_inc(x_20);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_36);
x_38 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__6));
lean_inc(x_20);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_20);
lean_ctor_set(x_39, 1, x_38);
x_40 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8));
x_41 = l_Array_append___redArg(x_25, x_8);
lean_dec_ref(x_8);
lean_inc(x_20);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_24);
lean_ctor_set(x_42, 2, x_41);
lean_inc(x_20);
x_43 = l_Lean_Syntax_node1(x_20, x_40, x_42);
x_44 = l_Lean_Syntax_node6(x_20, x_22, x_23, x_26, x_29, x_37, x_39, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_4);
x_46 = 1;
x_47 = l_Lean_Elab_Term_elabTerm(x_44, x_45, x_46, x_46, x_10, x_11, x_12, x_13, x_14, x_15);
return x_47;
}
block_65:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Array_append___redArg(x_25, x_49);
lean_dec_ref(x_49);
lean_inc(x_20);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_24);
lean_ctor_set(x_51, 2, x_50);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
lean_dec_ref(x_2);
x_53 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__9));
x_54 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10));
x_55 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11));
lean_inc(x_20);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_20);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_20);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_53);
x_58 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12));
lean_inc(x_20);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_20);
lean_ctor_set(x_59, 1, x_58);
x_60 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13));
lean_inc(x_20);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_20);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_20);
x_62 = l_Lean_Syntax_node5(x_20, x_54, x_56, x_57, x_59, x_52, x_61);
x_63 = l_Array_mkArray1___redArg(x_62);
x_26 = x_51;
x_27 = x_63;
goto block_48;
}
else
{
lean_object* x_64; 
lean_dec(x_2);
x_64 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_26 = x_51;
x_27 = x_64;
goto block_48;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_array_fget(x_8, x_7);
x_80 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19));
lean_inc(x_79);
x_81 = l_Lean_Syntax_isOfKind(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_unsigned_to_nat(1u);
x_84 = l_Lean_Syntax_getArg(x_79, x_83);
lean_inc(x_84);
x_85 = l_Lean_Syntax_matchesNull(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_84);
lean_dec(x_79);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Syntax_getArg(x_84, x_87);
lean_dec(x_84);
x_89 = l_Lean_Syntax_getArgs(x_88);
lean_dec(x_88);
x_90 = l_Lean_Syntax_TSepArray_getElems___redArg(x_89);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_91 = l_Lean_Elab_Do_getPatternsVarsEx(x_90, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc_ref(x_14);
x_93 = l_Lean_Elab_Do_checkMutVarsForShadowing(x_92, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_93);
x_94 = lean_box(x_5);
lean_inc_ref(x_6);
x_95 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___boxed), 20, 11);
lean_closure_set(x_95, 0, x_89);
lean_closure_set(x_95, 1, x_80);
lean_closure_set(x_95, 2, x_7);
lean_closure_set(x_95, 3, x_83);
lean_closure_set(x_95, 4, x_8);
lean_closure_set(x_95, 5, x_1);
lean_closure_set(x_95, 6, x_2);
lean_closure_set(x_95, 7, x_3);
lean_closure_set(x_95, 8, x_4);
lean_closure_set(x_95, 9, x_94);
lean_closure_set(x_95, 10, x_6);
x_96 = lean_unsigned_to_nat(3u);
x_97 = l_Lean_Syntax_getArg(x_79, x_96);
lean_dec(x_79);
x_98 = lean_box(x_5);
x_99 = lean_box(x_85);
lean_inc(x_97);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__1___boxed), 13, 4);
lean_closure_set(x_100, 0, x_98);
lean_closure_set(x_100, 1, x_97);
lean_closure_set(x_100, 2, x_6);
lean_closure_set(x_100, 3, x_99);
x_101 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__21);
x_102 = lean_array_to_list(x_90);
x_103 = lean_box(0);
x_104 = l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__2(x_102, x_103);
x_105 = l_Lean_MessageData_ofList(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Elab_Do_doElabToSyntaxWithExpectedType___redArg(x_106, x_100, x_95, x_97, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_97);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec(x_79);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_93);
if (x_108 == 0)
{
return x_93;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_93, 0);
lean_inc(x_109);
lean_dec(x_93);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec(x_79);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_91);
if (x_111 == 0)
{
return x_91;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
lean_dec(x_91);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_18, 5);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__0));
lean_inc(x_23);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2));
x_27 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3);
x_28 = l_Array_append___redArg(x_27, x_1);
lean_inc(x_23);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_23);
x_30 = l_Lean_Syntax_node1(x_23, x_26, x_29);
x_31 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__4));
lean_inc(x_23);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Syntax_node4(x_23, x_2, x_25, x_30, x_32, x_12);
x_34 = lean_nat_add(x_3, x_4);
x_35 = lean_array_fset(x_5, x_3, x_33);
x_36 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop(x_6, x_7, x_8, x_9, x_10, x_11, x_34, x_35, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_36;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
x_18 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_1, lean_box(0));
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_2(x_3, x_1, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unbox(x_5);
if (x_6 == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_2, lean_box(0));
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_apply_2(x_4, x_2, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(x_3);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(x_3);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop(x_1, x_2, x_3, x_4, x_5, x_8, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
x_18 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_83; uint8_t x_84; 
x_83 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9));
lean_inc(x_1);
x_84 = l_Lean_Syntax_isOfKind(x_1, x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_215; uint8_t x_216; 
x_86 = lean_unsigned_to_nat(0u);
x_168 = lean_unsigned_to_nat(1u);
x_215 = l_Lean_Syntax_getArg(x_1, x_168);
x_216 = l_Lean_Syntax_isNone(x_215);
if (x_216 == 0)
{
uint8_t x_217; 
lean_inc(x_215);
x_217 = l_Lean_Syntax_matchesNull(x_215, x_168);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_215);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_218 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = l_Lean_Syntax_getArg(x_215, x_86);
lean_dec(x_215);
x_220 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17));
lean_inc(x_219);
x_221 = l_Lean_Syntax_isOfKind(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_219);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_222 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_unsigned_to_nat(3u);
x_224 = l_Lean_Syntax_getArg(x_219, x_223);
lean_dec(x_219);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_192 = x_225;
x_193 = x_3;
x_194 = x_4;
x_195 = x_5;
x_196 = x_6;
x_197 = x_7;
x_198 = x_8;
x_199 = x_9;
x_200 = lean_box(0);
goto block_214;
}
}
}
else
{
lean_object* x_226; 
lean_dec(x_215);
x_226 = lean_box(0);
x_192 = x_226;
x_193 = x_3;
x_194 = x_4;
x_195 = x_5;
x_196 = x_6;
x_197 = x_7;
x_198 = x_8;
x_199 = x_9;
x_200 = lean_box(0);
goto block_214;
}
block_114:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_106 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_105, x_102);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_box(x_104);
x_109 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__1___boxed), 16, 7);
lean_closure_set(x_109, 0, x_92);
lean_closure_set(x_109, 1, x_90);
lean_closure_set(x_109, 2, x_88);
lean_closure_set(x_109, 3, x_87);
lean_closure_set(x_109, 4, x_108);
lean_closure_set(x_109, 5, x_86);
lean_closure_set(x_109, 6, x_91);
x_110 = lean_unbox(x_107);
lean_dec(x_107);
if (x_110 == 0)
{
x_11 = x_89;
x_12 = x_93;
x_13 = x_104;
x_14 = x_100;
x_15 = x_109;
x_16 = x_103;
x_17 = x_95;
x_18 = x_94;
x_19 = x_101;
x_20 = x_98;
x_21 = x_99;
x_22 = x_102;
x_23 = x_96;
x_24 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_111; 
x_111 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__11);
if (x_104 == 0)
{
lean_object* x_112; 
x_112 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__12));
x_49 = x_89;
x_50 = x_93;
x_51 = lean_box(0);
x_52 = x_104;
x_53 = x_98;
x_54 = x_105;
x_55 = x_109;
x_56 = x_103;
x_57 = x_102;
x_58 = x_111;
x_59 = x_94;
x_60 = x_95;
x_61 = x_96;
x_62 = x_99;
x_63 = x_100;
x_64 = x_101;
x_65 = x_112;
goto block_82;
}
else
{
lean_object* x_113; 
x_113 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__13));
x_49 = x_89;
x_50 = x_93;
x_51 = lean_box(0);
x_52 = x_104;
x_53 = x_98;
x_54 = x_105;
x_55 = x_109;
x_56 = x_103;
x_57 = x_102;
x_58 = x_111;
x_59 = x_94;
x_60 = x_95;
x_61 = x_96;
x_62 = x_99;
x_63 = x_100;
x_64 = x_101;
x_65 = x_113;
goto block_82;
}
}
}
block_135:
{
lean_object* x_133; uint8_t x_134; 
x_133 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15));
x_134 = l_Lean_Syntax_isOfKind(x_132, x_133);
if (x_134 == 0)
{
x_87 = x_115;
x_88 = x_116;
x_89 = x_117;
x_90 = x_119;
x_91 = x_120;
x_92 = x_121;
x_93 = x_122;
x_94 = x_124;
x_95 = x_125;
x_96 = x_126;
x_97 = lean_box(0);
x_98 = x_127;
x_99 = x_128;
x_100 = x_129;
x_101 = x_131;
x_102 = x_130;
x_103 = x_123;
x_104 = x_134;
goto block_114;
}
else
{
x_87 = x_115;
x_88 = x_116;
x_89 = x_117;
x_90 = x_119;
x_91 = x_120;
x_92 = x_121;
x_93 = x_122;
x_94 = x_124;
x_95 = x_125;
x_96 = x_126;
x_97 = lean_box(0);
x_98 = x_127;
x_99 = x_128;
x_100 = x_129;
x_101 = x_131;
x_102 = x_130;
x_103 = x_123;
x_104 = x_84;
goto block_114;
}
}
block_167:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_unsigned_to_nat(6u);
x_148 = l_Lean_Syntax_getArg(x_1, x_147);
x_149 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8));
lean_inc(x_148);
x_150 = l_Lean_Syntax_isOfKind(x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_2);
lean_dec(x_1);
x_151 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_138, 3);
lean_inc_ref(x_152);
lean_inc_ref(x_138);
lean_inc_ref(x_152);
x_153 = l_Lean_Elab_Do_mkMonadicType___redArg(x_152, x_138);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
lean_inc(x_141);
lean_inc_ref(x_143);
lean_inc(x_139);
lean_inc_ref(x_142);
lean_inc(x_140);
lean_inc_ref(x_137);
lean_inc(x_1);
x_155 = l_Lean_Elab_Do_inferControlInfoElem(x_1, x_137, x_140, x_142, x_139, x_143, x_141);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = lean_unsigned_to_nat(4u);
x_158 = l_Lean_Syntax_getArg(x_1, x_157);
lean_dec(x_1);
x_159 = l_Lean_Syntax_getArg(x_148, x_86);
lean_dec(x_148);
x_160 = l_Lean_Syntax_getArgs(x_159);
lean_dec(x_159);
x_161 = l_Lean_Syntax_getArgs(x_158);
lean_dec(x_158);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_162; 
x_162 = lean_box(0);
lean_inc_ref(x_152);
x_115 = x_154;
x_116 = x_161;
x_117 = x_150;
x_118 = lean_box(0);
x_119 = x_146;
x_120 = x_160;
x_121 = x_144;
x_122 = x_152;
x_123 = x_156;
x_124 = x_137;
x_125 = x_138;
x_126 = x_141;
x_127 = x_142;
x_128 = x_139;
x_129 = x_152;
x_130 = x_143;
x_131 = x_140;
x_132 = x_162;
goto block_135;
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_136, 0);
lean_inc(x_163);
lean_dec_ref(x_136);
lean_inc_ref(x_152);
x_115 = x_154;
x_116 = x_161;
x_117 = x_150;
x_118 = lean_box(0);
x_119 = x_146;
x_120 = x_160;
x_121 = x_144;
x_122 = x_152;
x_123 = x_156;
x_124 = x_137;
x_125 = x_138;
x_126 = x_141;
x_127 = x_142;
x_128 = x_139;
x_129 = x_152;
x_130 = x_143;
x_131 = x_140;
x_132 = x_163;
goto block_135;
}
}
else
{
uint8_t x_164; 
lean_dec(x_154);
lean_dec_ref(x_152);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_2);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_155);
if (x_164 == 0)
{
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
lean_dec(x_155);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
else
{
lean_dec_ref(x_152);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_153;
}
}
}
block_191:
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_unsigned_to_nat(3u);
x_180 = l_Lean_Syntax_getArg(x_1, x_179);
x_181 = l_Lean_Syntax_isNone(x_180);
if (x_181 == 0)
{
uint8_t x_182; 
lean_inc(x_180);
x_182 = l_Lean_Syntax_matchesNull(x_180, x_168);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_180);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec(x_1);
x_183 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = l_Lean_Syntax_getArg(x_180, x_86);
lean_dec(x_180);
x_185 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__10));
lean_inc(x_184);
x_186 = l_Lean_Syntax_isOfKind(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_184);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_2);
lean_dec(x_1);
x_187 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Lean_Syntax_getArg(x_184, x_179);
lean_dec(x_184);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_136 = x_169;
x_137 = x_172;
x_138 = x_171;
x_139 = x_175;
x_140 = x_173;
x_141 = x_177;
x_142 = x_174;
x_143 = x_176;
x_144 = x_170;
x_145 = lean_box(0);
x_146 = x_189;
goto block_167;
}
}
}
else
{
lean_object* x_190; 
lean_dec(x_180);
x_190 = lean_box(0);
x_136 = x_169;
x_137 = x_172;
x_138 = x_171;
x_139 = x_175;
x_140 = x_173;
x_141 = x_177;
x_142 = x_174;
x_143 = x_176;
x_144 = x_170;
x_145 = lean_box(0);
x_146 = x_190;
goto block_167;
}
}
block_214:
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_unsigned_to_nat(2u);
x_202 = l_Lean_Syntax_getArg(x_1, x_201);
x_203 = l_Lean_Syntax_isNone(x_202);
if (x_203 == 0)
{
uint8_t x_204; 
lean_inc(x_202);
x_204 = l_Lean_Syntax_matchesNull(x_202, x_168);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_202);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec(x_192);
lean_dec_ref(x_2);
lean_dec(x_1);
x_205 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = l_Lean_Syntax_getArg(x_202, x_86);
lean_dec(x_202);
x_207 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16));
lean_inc(x_206);
x_208 = l_Lean_Syntax_isOfKind(x_206, x_207);
if (x_208 == 0)
{
lean_object* x_209; 
lean_dec(x_206);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec_ref(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_193);
lean_dec(x_192);
lean_dec_ref(x_2);
lean_dec(x_1);
x_209 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_unsigned_to_nat(3u);
x_211 = l_Lean_Syntax_getArg(x_206, x_210);
lean_dec(x_206);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_169 = x_192;
x_170 = x_212;
x_171 = x_193;
x_172 = x_194;
x_173 = x_195;
x_174 = x_196;
x_175 = x_197;
x_176 = x_198;
x_177 = x_199;
x_178 = lean_box(0);
goto block_191;
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_202);
x_213 = lean_box(0);
x_169 = x_192;
x_170 = x_213;
x_171 = x_193;
x_172 = x_194;
x_173 = x_195;
x_174 = x_196;
x_175 = x_197;
x_176 = x_198;
x_177 = x_199;
x_178 = lean_box(0);
goto block_191;
}
}
}
block_48:
{
if (x_13 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_14);
lean_dec_ref(x_12);
x_25 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_2, x_16, x_15, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_box(x_11);
lean_inc_ref(x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___lam__0___boxed), 8, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_12);
lean_closure_set(x_28, 2, x_27);
x_29 = 0;
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_30 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_spec__0___redArg(x_28, x_29, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_14);
x_33 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_2, x_16, x_15, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_inc_ref(x_26);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_2);
x_34 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__1);
x_35 = l_Lean_indentExpr(x_14);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__3);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_26);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_40, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
block_82:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = l_Lean_MessageData_ofFormat(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__5);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc_ref(x_63);
x_72 = l_Lean_MessageData_ofExpr(x_63);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__7);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc_ref(x_66);
x_76 = l_Lean_MessageData_ofExpr(x_66);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_54, x_77, x_53, x_62, x_57, x_61);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_11 = x_49;
x_12 = x_50;
x_13 = x_52;
x_14 = x_63;
x_15 = x_55;
x_16 = x_56;
x_17 = x_60;
x_18 = x_59;
x_19 = x_64;
x_20 = x_53;
x_21 = x_62;
x_22 = x_57;
x_23 = x_61;
x_24 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_79; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
lean_dec_ref(x_50);
lean_dec_ref(x_2);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = 1;
x_21 = lean_array_uget_borrowed(x_1, x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_21, x_22);
x_24 = l_Lean_Elab_Term_isAtomicDiscr(x_23, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(x_12);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_free_object(x_24);
x_13 = x_11;
x_14 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_12);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
x_13 = x_11;
x_14 = lean_box(0);
goto block_20;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec_ref(x_24);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_13 = x_34;
x_14 = lean_box(0);
goto block_20;
}
else
{
return x_24;
}
}
block_20:
{
if (x_13 == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(x_12);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_34; 
x_20 = lean_array_uget_borrowed(x_1, x_3);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1));
lean_inc(x_20);
x_34 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
if (lean_obj_tag(x_35) == 0)
{
lean_dec_ref(x_35);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_106; uint8_t x_107; 
x_39 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Syntax_getArg(x_20, x_39);
x_107 = l_Lean_Syntax_isNone(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_unsigned_to_nat(2u);
lean_inc(x_106);
x_109 = l_Lean_Syntax_matchesNull(x_106, x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_106);
x_110 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
if (lean_obj_tag(x_110) == 0)
{
lean_dec_ref(x_110);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_111; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Syntax_getArg(x_106, x_39);
lean_dec(x_106);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_72 = x_115;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_10;
x_79 = lean_box(0);
goto block_105;
}
}
else
{
lean_object* x_116; 
lean_dec(x_106);
x_116 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_72 = x_116;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_10;
x_79 = lean_box(0);
goto block_105;
}
block_71:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
x_52 = l_Lean_Elab_Term_elabTerm(x_42, x_51, x_34, x_34, x_44, x_45, x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc_ref(x_48);
x_54 = l_Lean_Elab_Term_exprToSyntax(x_53, x_44, x_45, x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_48, 5);
lean_inc(x_56);
lean_dec_ref(x_48);
x_57 = l_Lean_SourceInfo_fromRef(x_56, x_40);
lean_dec(x_56);
x_58 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2));
x_59 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
lean_dec_ref(x_41);
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__2));
lean_inc(x_57);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Array_mkArray2___redArg(x_60, x_62);
x_22 = lean_box(0);
x_23 = x_55;
x_24 = x_57;
x_25 = x_58;
x_26 = x_43;
x_27 = x_59;
x_28 = x_63;
goto block_33;
}
else
{
lean_object* x_64; 
lean_dec(x_41);
x_64 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_22 = lean_box(0);
x_23 = x_55;
x_24 = x_57;
x_25 = x_58;
x_26 = x_43;
x_27 = x_59;
x_28 = x_64;
goto block_33;
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_48);
lean_dec_ref(x_43);
lean_dec(x_41);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_65 = !lean_is_exclusive(x_54);
if (x_65 == 0)
{
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
lean_dec(x_41);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
block_105:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = l_Lean_Syntax_getArg(x_20, x_80);
lean_inc(x_81);
x_82 = l_Lean_Elab_Term_isAtomicDiscr(x_81, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_86 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_85, x_77);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_unbox(x_83);
lean_dec(x_83);
x_40 = x_89;
x_41 = x_72;
x_42 = x_81;
x_43 = x_4;
x_44 = x_73;
x_45 = x_74;
x_46 = x_75;
x_47 = x_76;
x_48 = x_77;
x_49 = x_78;
x_50 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__4);
lean_inc(x_81);
x_91 = l_Lean_MessageData_ofSyntax(x_81);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_85, x_92, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec_ref(x_93);
x_94 = lean_unbox(x_83);
lean_dec(x_83);
x_40 = x_94;
x_41 = x_72;
x_42 = x_81;
x_43 = x_4;
x_44 = x_73;
x_45 = x_74;
x_46 = x_75;
x_47 = x_76;
x_48 = x_77;
x_49 = x_78;
x_50 = lean_box(0);
goto block_71;
}
else
{
uint8_t x_95; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
return x_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_98 = !lean_is_exclusive(x_86);
if (x_98 == 0)
{
return x_86;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_86, 0);
lean_inc(x_99);
lean_dec(x_86);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_inc(x_20);
x_101 = lean_array_push(x_4, x_20);
x_12 = x_101;
x_13 = lean_box(0);
goto block_17;
}
}
else
{
uint8_t x_102; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_102 = !lean_is_exclusive(x_82);
if (x_102 == 0)
{
return x_82;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_82, 0);
lean_inc(x_103);
lean_dec(x_82);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
block_33:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Array_append___redArg(x_27, x_28);
lean_dec_ref(x_28);
lean_inc(x_24);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lean_Syntax_node2(x_24, x_21, x_30, x_23);
x_32 = lean_array_push(x_26, x_31);
x_12 = x_32;
x_13 = lean_box(0);
goto block_17;
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_48; uint8_t x_49; 
x_10 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_lt(x_10, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = x_50;
goto block_47;
}
else
{
if (x_49 == 0)
{
lean_object* x_51; 
x_51 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = x_51;
goto block_47;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
x_54 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg(x_1, x_52, x_53, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
x_57 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___lam__0(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = x_57;
goto block_47;
}
else
{
x_11 = x_54;
goto block_47;
}
}
}
block_47:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_11);
x_15 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0);
x_16 = lean_array_size(x_1);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(x_1, x_16, x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_28 = lean_box(0);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0);
x_32 = lean_array_size(x_1);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(x_1, x_32, x_33, x_31, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(x_1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__0);
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = lean_obj_once(&l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2, &l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__2);
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_20 = lean_box(0);
x_31 = lean_array_uget_borrowed(x_1, x_3);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1));
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_75; 
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
x_12 = x_20;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Syntax_getArg(x_31, x_76);
x_78 = l_Lean_Syntax_isNone(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_unsigned_to_nat(2u);
x_80 = l_Lean_Syntax_matchesNull(x_77, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_12 = x_20;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_81;
}
}
else
{
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = lean_box(0);
goto block_74;
}
}
else
{
lean_dec(x_77);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_10;
x_40 = lean_box(0);
goto block_74;
}
}
block_30:
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Term_tryPostponeIfMVar(x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_29);
x_12 = x_20;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_29;
}
}
block_74:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Syntax_getArg(x_31, x_41);
x_43 = lean_box(0);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
x_44 = l_Lean_Elab_Term_elabTerm(x_42, x_43, x_33, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_45);
x_46 = lean_infer_type(x_45, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_49 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(x_48, x_38);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_dec(x_45);
x_21 = x_47;
x_22 = x_34;
x_23 = x_35;
x_24 = x_36;
x_25 = x_37;
x_26 = x_38;
x_27 = x_39;
x_28 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_52; 
lean_inc(x_47);
x_52 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(x_47, x_37);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__1);
x_55 = l_Lean_MessageData_ofExpr(x_45);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___closed__3);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofExpr(x_53);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(x_48, x_60, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_21 = x_47;
x_22 = x_34;
x_23 = x_35;
x_24 = x_36;
x_25 = x_37;
x_26 = x_38;
x_27 = x_39;
x_28 = lean_box(0);
goto block_30;
}
else
{
lean_dec(x_47);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_45);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
return x_46;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
lean_dec(x_46);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_71 = !lean_is_exclusive(x_44);
if (x_71 == 0)
{
return x_44;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_44, 0);
lean_inc(x_72);
lean_dec(x_44);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__4(x_1, x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
}
else
{
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 10);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 11);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_addMacroScope(x_5, x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__2));
x_5 = l_Lean_Core_withFreshMacroScope___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg(x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_FVarId_getUserName___redArg(x_9, x_4, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Core_mkFreshUserName(x_11, x_6, x_7);
return x_12;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg(x_6, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_29; 
x_29 = lean_usize_dec_lt(x_3, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_array_uget_borrowed(x_1, x_3);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1));
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Syntax_getArg(x_31, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(2u);
lean_inc(x_73);
x_76 = l_Lean_Syntax_matchesNull(x_73, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
x_77 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_Syntax_getArg(x_73, x_72);
lean_dec(x_73);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = x_82;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = lean_box(0);
goto block_67;
}
}
else
{
lean_object* x_83; 
lean_dec(x_73);
x_83 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = x_83;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = lean_box(0);
goto block_67;
}
}
block_67:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_31, x_42);
x_44 = lean_box(0);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
x_45 = l_Lean_Elab_Term_elabTerm(x_43, x_44, x_33, x_33, x_35, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__2___redArg(x_46, x_38);
lean_dec(x_38);
if (lean_obj_tag(x_47) == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_48; 
lean_dec(x_40);
lean_dec_ref(x_39);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_18 = lean_box(0);
x_19 = x_48;
x_20 = x_44;
goto block_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec_ref(x_34);
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__1));
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_dec(x_40);
lean_dec_ref(x_39);
x_24 = x_49;
x_25 = x_50;
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___closed__3));
x_54 = l_Lean_Core_mkFreshUserName(x_53, x_39, x_40);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = 0;
x_57 = l_Lean_mkIdentFrom(x_50, x_55, x_56);
lean_dec(x_50);
x_24 = x_49;
x_25 = x_57;
x_26 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_58; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_61 = !lean_is_exclusive(x_47);
if (x_61 == 0)
{
return x_47;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_45, 0);
lean_inc(x_65);
lean_dec(x_45);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_push(x_4, x_21);
x_12 = x_22;
x_13 = lean_box(0);
goto block_17;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_18 = lean_box(0);
x_19 = x_24;
x_20 = x_27;
goto block_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___closed__0);
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs_spec__0(x_1, x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_fget_borrowed(x_2, x_4);
x_17 = lean_array_get_borrowed(x_15, x_3, x_4);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = lean_box(x_13);
x_21 = lean_box(x_13);
lean_inc(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPatternElabConfig___boxed), 9, 2);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_22);
x_24 = 1;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_array_push(x_5, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_4 = x_29;
x_5 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_2);
x_12 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*8 + 2, x_12);
lean_inc_ref(x_7);
x_13 = l_Lean_Elab_Term_checkNumPatterns(x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(x_15, x_14, x_2, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec_ref(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_26 = lean_ctor_get(x_3, 2);
x_27 = lean_ctor_get(x_3, 3);
x_28 = lean_ctor_get(x_3, 4);
x_29 = lean_ctor_get(x_3, 5);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 3);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 4);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 5);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 6);
x_34 = lean_ctor_get(x_3, 6);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 7);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 8);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 9);
x_38 = lean_ctor_get(x_3, 7);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_39 = lean_array_get_size(x_2);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set(x_41, 4, x_28);
lean_ctor_set(x_41, 5, x_29);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*8, x_24);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 1, x_25);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 2, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 3, x_30);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 4, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 5, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 6, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 7, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 8, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 9, x_37);
lean_inc_ref(x_7);
x_42 = l_Lean_Elab_Term_checkNumPatterns(x_39, x_1, x_41, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_47 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(x_44, x_43, x_2, x_45, x_46, x_41, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_41);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 5, x_13);
x_14 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
x_26 = lean_ctor_get(x_8, 11);
x_27 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_28 = lean_ctor_get(x_8, 12);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_30 = lean_ctor_get(x_8, 13);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_31 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_17);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set(x_32, 4, x_19);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_21);
lean_ctor_set(x_32, 7, x_22);
lean_ctor_set(x_32, 8, x_23);
lean_ctor_set(x_32, 9, x_24);
lean_ctor_set(x_32, 10, x_25);
lean_ctor_set(x_32, 11, x_26);
lean_ctor_set(x_32, 12, x_28);
lean_ctor_set(x_32, 13, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_29);
x_33 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns(x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_9);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_to_list(x_3);
x_14 = lean_array_to_list(x_4);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_apply_8(x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget_borrowed(x_1, x_7);
x_9 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1));
x_10 = 0;
lean_inc(x_8);
x_11 = l_Lean_mkForall(x_9, x_10, x_8, x_4);
x_2 = x_7;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_withElaboratedLHS_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc_ref(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_4);
x_14 = 1;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_38; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_18 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__1___redArg(x_17, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Do_withElaboratedLHS___redArg___lam__1___boxed), 12, 2);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_5);
x_38 = lean_unbox(x_19);
lean_dec(x_19);
if (x_38 == 0)
{
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_obj_once(&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4, &l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4_once, _init_l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__4);
lean_inc(x_16);
x_40 = lean_array_to_list(x_16);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___at___00Lean_Elab_Do_withElaboratedLHS_spec__1(x_40, x_41);
x_43 = l_Lean_MessageData_ofList(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__3___redArg(x_17, x_44, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = lean_box(0);
goto block_37;
}
else
{
uint8_t x_46; 
lean_dec_ref(x_20);
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_obj_once(&l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2, &l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2_once, _init_l_Lean_Elab_Do_withElaboratedLHS___redArg___closed__2);
x_29 = lean_array_get_size(x_4);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_4);
x_32 = l_Lean_Elab_Term_ToDepElimPattern_main___redArg(x_1, x_16, x_28, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_usize_of_nat(x_29);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_withElaboratedLHS_spec__0(x_4, x_33, x_34, x_28);
lean_dec_ref(x_4);
x_36 = l_Lean_Elab_Term_ToDepElimPattern_main___redArg(x_1, x_16, x_35, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_36;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_15, 0);
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Do_withElaboratedLHS___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Do_withElaboratedLHS___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_withElaboratedLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Do_withElaboratedLHS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l_Lean_Meta_withLocalInstancesImp___redArg(x_1, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_LocalDecl_toExpr(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_inc(x_1);
x_66 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_1, x_13);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_dec(x_8);
x_38 = x_7;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_14;
x_45 = lean_box(0);
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__3);
x_70 = l_Lean_MessageData_ofSyntax(x_8);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_1);
x_72 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_1, x_71, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_38 = x_7;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_14;
x_45 = lean_box(0);
goto block_65;
}
else
{
uint8_t x_73; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_37:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_1);
x_27 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_1, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_1);
x_16 = x_21;
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___closed__1);
lean_inc_ref(x_21);
x_31 = l_Lean_MessageData_ofExpr(x_21);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_1, x_32, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_16 = x_21;
x_17 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_34; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
block_65:
{
uint8_t x_46; lean_object* x_47; 
x_46 = 1;
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
x_47 = l_Lean_Elab_Do_elabDoSeq(x_3, x_4, x_46, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_array_mk(x_5);
x_50 = lean_array_size(x_49);
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__0(x_50, x_51, x_49);
x_53 = l_Array_append___redArg(x_52, x_6);
x_54 = l_Array_isEmpty___redArg(x_53);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; 
x_55 = 1;
x_56 = l_Lean_Meta_mkLambdaFVars(x_53, x_48, x_54, x_46, x_54, x_46, x_55, x_41, x_42, x_43, x_44);
lean_dec_ref(x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_21 = x_57;
x_22 = x_41;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = lean_box(0);
goto block_37;
}
else
{
uint8_t x_58; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec_ref(x_53);
x_61 = l_Lean_mkSimpleThunk(x_48);
x_21 = x_61;
x_22 = x_41;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_62; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
return x_47;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_5);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__0___boxed), 15, 8);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_8);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
x_17 = l_Lean_Meta_withLocalInstances___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__1___redArg(x_5, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__1___boxed), 15, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_15);
lean_closure_set(x_17, 5, x_4);
lean_closure_set(x_17, 6, x_5);
x_18 = l_Lean_Elab_Term_withEqs___redArg(x_6, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec_ref(x_1);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__2___boxed), 14, 6);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_5);
x_19 = l_Lean_Elab_Do_withElaboratedLHS___redArg(x_7, x_15, x_16, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofSyntax(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofSyntax(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_10, 5);
x_16 = l_Lean_replaceRef(x_14, x_15);
lean_dec(x_15);
lean_ctor_set(x_10, 5, x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_Elab_Term_collectPatternVars___redArg(x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_34 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_22, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_free_object(x_18);
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1);
lean_inc(x_20);
x_38 = lean_array_to_list(x_20);
x_39 = lean_box(0);
x_40 = l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__2(x_38, x_39);
x_41 = l_Lean_MessageData_ofList(x_40);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_41);
lean_ctor_set(x_18, 0, x_37);
x_42 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_22, x_18, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3___boxed), 14, 6);
lean_closure_set(x_31, 0, x_21);
lean_closure_set(x_31, 1, x_22);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_23);
lean_closure_set(x_31, 4, x_1);
lean_closure_set(x_31, 5, x_2);
x_32 = l_Lean_Elab_Term_withPatternVars___redArg(x_20, x_31, x_24, x_25, x_26, x_27, x_28, x_29);
return x_32;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_60 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_48, x_10);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1);
lean_inc(x_46);
x_64 = lean_array_to_list(x_46);
x_65 = lean_box(0);
x_66 = l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__2(x_64, x_65);
x_67 = l_Lean_MessageData_ofList(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_48, x_68, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
block_59:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3___boxed), 14, 6);
lean_closure_set(x_57, 0, x_47);
lean_closure_set(x_57, 1, x_48);
lean_closure_set(x_57, 2, x_4);
lean_closure_set(x_57, 3, x_49);
lean_closure_set(x_57, 4, x_1);
lean_closure_set(x_57, 5, x_2);
x_58 = l_Lean_Elab_Term_withPatternVars___redArg(x_46, x_57, x_50, x_51, x_52, x_53, x_54, x_55);
return x_58;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_17);
if (x_73 == 0)
{
return x_17;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_17, 0);
lean_inc(x_74);
lean_dec(x_17);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_10, 0);
x_78 = lean_ctor_get(x_10, 1);
x_79 = lean_ctor_get(x_10, 2);
x_80 = lean_ctor_get(x_10, 3);
x_81 = lean_ctor_get(x_10, 4);
x_82 = lean_ctor_get(x_10, 5);
x_83 = lean_ctor_get(x_10, 6);
x_84 = lean_ctor_get(x_10, 7);
x_85 = lean_ctor_get(x_10, 8);
x_86 = lean_ctor_get(x_10, 9);
x_87 = lean_ctor_get(x_10, 10);
x_88 = lean_ctor_get(x_10, 11);
x_89 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_90 = lean_ctor_get(x_10, 12);
x_91 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_92 = lean_ctor_get(x_10, 13);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_10);
x_93 = l_Lean_replaceRef(x_76, x_82);
lean_dec(x_82);
x_94 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_94, 1, x_78);
lean_ctor_set(x_94, 2, x_79);
lean_ctor_set(x_94, 3, x_80);
lean_ctor_set(x_94, 4, x_81);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_83);
lean_ctor_set(x_94, 7, x_84);
lean_ctor_set(x_94, 8, x_85);
lean_ctor_set(x_94, 9, x_86);
lean_ctor_set(x_94, 10, x_87);
lean_ctor_set(x_94, 11, x_88);
lean_ctor_set(x_94, 12, x_90);
lean_ctor_set(x_94, 13, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*14, x_89);
lean_ctor_set_uint8(x_94, sizeof(void*)*14 + 1, x_91);
lean_inc(x_11);
lean_inc_ref(x_94);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_95 = l_Lean_Elab_Term_collectPatternVars___redArg(x_3, x_6, x_7, x_8, x_9, x_94, x_11);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_112 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_100, x_94);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_dec(x_99);
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_94;
x_107 = x_11;
x_108 = lean_box(0);
goto block_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___closed__1);
lean_inc(x_97);
x_116 = lean_array_to_list(x_97);
x_117 = lean_box(0);
x_118 = l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt_spec__2(x_116, x_117);
x_119 = l_Lean_MessageData_ofList(x_118);
if (lean_is_scalar(x_99)) {
 x_120 = lean_alloc_ctor(7, 2, 0);
} else {
 x_120 = x_99;
 lean_ctor_set_tag(x_120, 7);
}
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_100, x_120, x_8, x_9, x_94, x_11);
if (lean_obj_tag(x_121) == 0)
{
lean_dec_ref(x_121);
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_94;
x_107 = x_11;
x_108 = lean_box(0);
goto block_111;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec_ref(x_94);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
block_111:
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___lam__3___boxed), 14, 6);
lean_closure_set(x_109, 0, x_98);
lean_closure_set(x_109, 1, x_100);
lean_closure_set(x_109, 2, x_4);
lean_closure_set(x_109, 3, x_101);
lean_closure_set(x_109, 4, x_1);
lean_closure_set(x_109, 5, x_2);
x_110 = l_Lean_Elab_Term_withPatternVars___redArg(x_97, x_109, x_102, x_103, x_104, x_105, x_106, x_107);
return x_110;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_94);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_95, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_126 = x_95;
} else {
 lean_dec_ref(x_95);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget_borrowed(x_6, x_5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
lean_inc(x_17);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlt(x_1, x_2, x_17, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uset(x_6, x_5, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_24 = lean_array_uset(x_21, x_5, x_19);
x_5 = x_23;
x_6 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___closed__0));
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_1(x_2, lean_box(0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_6, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0___boxed), 11, 5);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_7);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_9);
lean_closure_set(x_16, 4, x_10);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_16, x_5, x_6, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___lam__0___boxed), 11, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_7);
lean_closure_set(x_15, 3, x_8);
lean_closure_set(x_15, 4, x_9);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_15, x_5, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_5);
x_17 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(x_1, x_15, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_1(x_2, lean_box(0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
x_20 = lean_ctor_get(x_8, 3);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
x_24 = lean_ctor_get(x_8, 7);
x_25 = lean_ctor_get(x_8, 8);
x_26 = lean_ctor_get(x_8, 9);
x_27 = lean_ctor_get(x_8, 10);
x_28 = lean_ctor_get(x_8, 11);
x_29 = lean_ctor_get(x_8, 12);
x_30 = lean_ctor_get(x_8, 13);
x_31 = lean_nat_dec_eq(x_20, x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_20, x_32);
lean_dec(x_20);
lean_ctor_set(x_8, 3, x_33);
x_34 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
x_11 = x_34;
goto block_15;
}
else
{
lean_object* x_35; 
lean_free_object(x_8);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(x_22);
x_11 = x_35;
goto block_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
x_39 = lean_ctor_get(x_8, 3);
x_40 = lean_ctor_get(x_8, 4);
x_41 = lean_ctor_get(x_8, 5);
x_42 = lean_ctor_get(x_8, 6);
x_43 = lean_ctor_get(x_8, 7);
x_44 = lean_ctor_get(x_8, 8);
x_45 = lean_ctor_get(x_8, 9);
x_46 = lean_ctor_get(x_8, 10);
x_47 = lean_ctor_get(x_8, 11);
x_48 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_49 = lean_ctor_get(x_8, 12);
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_51 = lean_ctor_get(x_8, 13);
lean_inc(x_51);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_52 = lean_nat_dec_eq(x_39, x_40);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_39, x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_37);
lean_ctor_set(x_55, 2, x_38);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_40);
lean_ctor_set(x_55, 5, x_41);
lean_ctor_set(x_55, 6, x_42);
lean_ctor_set(x_55, 7, x_43);
lean_ctor_set(x_55, 8, x_44);
lean_ctor_set(x_55, 9, x_45);
lean_ctor_set(x_55, 10, x_46);
lean_ctor_set(x_55, 11, x_47);
lean_ctor_set(x_55, 12, x_49);
lean_ctor_set(x_55, 13, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*14, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*14 + 1, x_50);
x_56 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_55, x_9, lean_box(0));
x_11 = x_56;
goto block_15;
}
else
{
lean_object* x_57; 
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(x_41);
x_11 = x_57;
goto block_15;
}
}
block_15:
{
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_ExprStructEq_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_ExprStructEq_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_ExprStructEq_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_1, x_18);
lean_inc(x_19);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_ExprStructEq_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget_borrowed(x_1, x_37);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_ExprStructEq_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_ExprStructEq_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
lean_inc(x_20);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_20);
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_ExprStructEq_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget_borrowed(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
lean_inc(x_52);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_52);
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_ref_take(x_1);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10___redArg(x_5, x_2, x_3);
x_7 = lean_st_ref_set(x_1, x_6);
x_8 = lean_box(0);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_ExprStructEq_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_ExprStructEq_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_1, x_8);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(x_2, x_3, x_4, x_5, x_6, x_18, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0(x_1, x_2, x_3, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
x_16 = lean_apply_9(x_2, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
case 1:
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_16);
lean_dec_ref(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec_ref(x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_6);
x_27 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_24);
x_28 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
default: 
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_6);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_6);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec_ref(x_7);
x_21 = lean_expr_instantiate_rev(x_18, x_6);
lean_dec_ref(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(x_3);
x_25 = lean_box(x_4);
x_26 = lean_box(x_5);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___lam__0___boxed), 17, 7);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_24);
lean_closure_set(x_27, 4, x_25);
lean_closure_set(x_27, 5, x_26);
lean_closure_set(x_27, 6, x_19);
x_28 = 0;
x_29 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(x_17, x_20, x_23, x_27, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_29;
}
else
{
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec_ref(x_7);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = 0;
x_34 = 1;
x_35 = 1;
x_36 = l_Lean_Meta_mkLambdaFVars(x_6, x_32, x_33, x_3, x_33, x_34, x_35, x_12, x_13, x_14, x_15);
lean_dec_ref(x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_38;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_36;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_1, x_8);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(x_2, x_3, x_4, x_5, x_6, x_18, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0(x_1, x_2, x_3, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_7) == 8)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_20);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*4 + 8);
lean_dec_ref(x_7);
x_22 = lean_expr_instantiate_rev(x_18, x_6);
lean_dec_ref(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_expr_instantiate_rev(x_19, x_6);
lean_dec_ref(x_19);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_26 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_box(x_3);
x_29 = lean_box(x_4);
x_30 = lean_box(x_5);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___lam__0___boxed), 17, 7);
lean_closure_set(x_31, 0, x_6);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_28);
lean_closure_set(x_31, 4, x_29);
lean_closure_set(x_31, 5, x_30);
lean_closure_set(x_31, 6, x_20);
x_32 = 0;
x_33 = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg(x_17, x_24, x_27, x_31, x_21, x_32, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_33;
}
else
{
lean_dec(x_24);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec_ref(x_7);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_35 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = 0;
x_38 = 1;
x_39 = l_Lean_Meta_mkLetFVars(x_6, x_36, x_3, x_37, x_38, x_12, x_13, x_14, x_15);
lean_dec_ref(x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_41;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_39;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_uget_borrowed(x_8, x_7);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_20);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_uset(x_8, x_7, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_27 = lean_array_uset(x_24, x_7, x_22);
x_7 = x_26;
x_8 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_array_fset(x_8, x_9, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_array_fset(x_8, x_9, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_8);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0(x_1, x_2, x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; uint8_t x_39; 
x_39 = lean_nat_dec_lt(x_8, x_1);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_array_fget_borrowed(x_9, x_8);
x_42 = lean_array_get_size(x_2);
x_43 = lean_nat_dec_lt(x_8, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_41);
x_44 = lean_box(x_5);
x_45 = lean_box(x_6);
x_46 = lean_box(x_7);
lean_inc(x_8);
lean_inc(x_10);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_47 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 17, 9);
lean_closure_set(x_47, 0, x_3);
lean_closure_set(x_47, 1, x_4);
lean_closure_set(x_47, 2, x_44);
lean_closure_set(x_47, 3, x_45);
lean_closure_set(x_47, 4, x_46);
lean_closure_set(x_47, 5, x_41);
lean_closure_set(x_47, 6, x_10);
lean_closure_set(x_47, 7, x_9);
lean_closure_set(x_47, 8, x_8);
x_19 = x_47;
goto block_38;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_fget_borrowed(x_2, x_8);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1 + 4);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_41);
x_50 = lean_box(x_5);
x_51 = lean_box(x_6);
x_52 = lean_box(x_7);
lean_inc(x_8);
lean_inc(x_10);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_53 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 17, 9);
lean_closure_set(x_53, 0, x_3);
lean_closure_set(x_53, 1, x_4);
lean_closure_set(x_53, 2, x_50);
lean_closure_set(x_53, 3, x_51);
lean_closure_set(x_53, 4, x_52);
lean_closure_set(x_53, 5, x_41);
lean_closure_set(x_53, 6, x_10);
lean_closure_set(x_53, 7, x_9);
lean_closure_set(x_53, 8, x_8);
x_19 = x_53;
goto block_38;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_9);
x_55 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 9, 1);
lean_closure_set(x_55, 0, x_54);
x_19 = x_55;
goto block_38;
}
}
}
block_38:
{
lean_object* x_20; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_20 = lean_apply_8(x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_8 = x_26;
x_9 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_8, x_32);
lean_dec(x_8);
x_8 = x_33;
x_9 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_57);
lean_dec_ref(x_6);
x_58 = lean_array_set(x_7, x_8, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_8, x_59);
lean_dec(x_8);
x_6 = x_56;
x_7 = x_58;
x_8 = x_60;
goto _start;
}
else
{
lean_dec(x_8);
if (x_5 == 0)
{
goto block_55;
}
else
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isConst(x_6);
if (x_62 == 0)
{
goto block_55;
}
else
{
x_18 = x_6;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_15;
x_26 = x_16;
x_27 = lean_box(0);
goto block_52;
}
}
}
block_52:
{
if (x_1 == 0)
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_array_size(x_7);
x_29 = 0;
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1(x_2, x_3, x_4, x_5, x_1, x_28, x_29, x_7, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_mkAppN(x_18, x_31);
lean_dec(x_31);
x_33 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_2, x_3, x_4, x_5, x_1, x_32, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_array_get_size(x_7);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_18);
x_38 = l_Lean_Meta_getFunInfoNArgs(x_18, x_37, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_40);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_42 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg(x_37, x_40, x_2, x_3, x_4, x_5, x_1, x_41, x_7, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_mkAppN(x_18, x_43);
lean_dec(x_43);
x_45 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_2, x_3, x_4, x_5, x_1, x_44, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
block_55:
{
lean_object* x_53; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_53 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_2, x_3, x_4, x_5, x_1, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_18 = x_54;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_15;
x_26 = x_16;
x_27 = lean_box(0);
goto block_52;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_16 = lean_apply_9(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_55; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_55);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_55);
return x_16;
}
case 1:
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_16);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_56);
lean_dec_ref(x_18);
x_57 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_56, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_57;
}
default: 
{
lean_object* x_58; 
lean_free_object(x_16);
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec_ref(x_18);
if (lean_obj_tag(x_58) == 0)
{
x_19 = x_2;
goto block_54;
}
else
{
lean_object* x_59; 
lean_dec_ref(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_19 = x_59;
goto block_54;
}
}
}
block_54:
{
switch (lean_obj_tag(x_19)) {
case 7:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(x_1, x_3, x_4, x_5, x_6, x_20, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
case 6:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_23 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(x_1, x_3, x_4, x_5, x_6, x_22, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_23;
}
case 8:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_25 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(x_1, x_3, x_4, x_5, x_6, x_24, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0);
x_27 = l_Lean_Expr_getAppNumArgs(x_19);
lean_inc(x_27);
x_28 = lean_mk_array(x_27, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_27, x_29);
lean_dec(x_27);
x_31 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8(x_6, x_1, x_3, x_4, x_5, x_19, x_28, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_31;
}
case 10:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_33);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_34 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ptr_addr(x_33);
x_37 = lean_ptr_addr(x_35);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_inc(x_32);
lean_dec_ref(x_19);
x_39 = l_Lean_Expr_mdata___override(x_32, x_35);
x_40 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_35);
x_41 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_41;
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_34;
}
}
case 11:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
x_44 = lean_ctor_get(x_19, 2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_44);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_45 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; size_t x_47; size_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ptr_addr(x_44);
x_48 = lean_ptr_addr(x_46);
x_49 = lean_usize_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_inc(x_43);
lean_inc(x_42);
lean_dec_ref(x_19);
x_50 = l_Lean_Expr_proj___override(x_42, x_43, x_46);
x_51 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_46);
x_52 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_52;
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_45;
}
}
default: 
{
lean_object* x_53; 
x_53 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_53;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_97);
lean_dec_ref(x_60);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
case 1:
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_2);
x_99 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_99);
lean_dec_ref(x_60);
x_100 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_99, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_100;
}
default: 
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_60, 0);
lean_inc(x_101);
lean_dec_ref(x_60);
if (lean_obj_tag(x_101) == 0)
{
x_61 = x_2;
goto block_96;
}
else
{
lean_object* x_102; 
lean_dec_ref(x_2);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_61 = x_102;
goto block_96;
}
}
}
block_96:
{
switch (lean_obj_tag(x_61)) {
case 7:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_63 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(x_1, x_3, x_4, x_5, x_6, x_62, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_63;
}
case 6:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_65 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(x_1, x_3, x_4, x_5, x_6, x_64, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_65;
}
case 8:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabPatterns___closed__0);
x_67 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(x_1, x_3, x_4, x_5, x_6, x_66, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_67;
}
case 5:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___closed__0);
x_69 = l_Lean_Expr_getAppNumArgs(x_61);
lean_inc(x_69);
x_70 = lean_mk_array(x_69, x_68);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_69, x_71);
lean_dec(x_69);
x_73 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8(x_6, x_1, x_3, x_4, x_5, x_61, x_70, x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_73;
}
case 10:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_75);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_76 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_75, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ptr_addr(x_75);
x_79 = lean_ptr_addr(x_77);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_inc(x_74);
lean_dec_ref(x_61);
x_81 = l_Lean_Expr_mdata___override(x_74, x_77);
x_82 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_77);
x_83 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_83;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_76;
}
}
case 11:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_61, 0);
x_85 = lean_ctor_get(x_61, 1);
x_86 = lean_ctor_get(x_61, 2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_86);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_87 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_3, x_4, x_5, x_6, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; size_t x_89; size_t x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ptr_addr(x_86);
x_90 = lean_ptr_addr(x_88);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_inc(x_85);
lean_inc(x_84);
lean_dec_ref(x_61);
x_92 = l_Lean_Expr_proj___override(x_84, x_85, x_88);
x_93 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_92, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_88);
x_94 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_94;
}
}
else
{
lean_dec_ref(x_61);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_87;
}
}
default: 
{
lean_object* x_95; 
x_95 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_95;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_16);
if (x_103 == 0)
{
return x_16;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_16, 0);
lean_inc(x_104);
lean_dec(x_16);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1(x_1, x_2, x_3, x_16, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_7);
x_17 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(lean_box(0), x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(x_19, x_6);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_17);
x_21 = lean_box(x_3);
x_22 = lean_box(x_4);
x_23 = lean_box(x_5);
lean_inc_ref(x_6);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___boxed), 15, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_6);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_23);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(x_27, 0, x_7);
lean_closure_set(x_27, 1, x_6);
lean_closure_set(x_27, 2, x_26);
x_28 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(lean_box(0), x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_26);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_25;
}
}
else
{
lean_object* x_35; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec_ref(x_20);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
lean_dec(x_17);
x_37 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(x_36, x_6);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_box(x_3);
x_39 = lean_box(x_4);
x_40 = lean_box(x_5);
lean_inc_ref(x_6);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__1___boxed), 15, 6);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_6);
lean_closure_set(x_41, 2, x_2);
lean_closure_set(x_41, 3, x_38);
lean_closure_set(x_41, 4, x_39);
lean_closure_set(x_41, 5, x_40);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_42 = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(x_44, 0, x_7);
lean_closure_set(x_44, 1, x_6);
lean_closure_set(x_44, 2, x_43);
x_45 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___lam__0(lean_box(0), x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_46 = x_45;
} else {
 lean_dec_ref(x_45);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_37, 0);
lean_inc(x_51);
lean_dec_ref(x_37);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_17, 0);
lean_inc(x_54);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0(x_1, x_2, x_3, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec_ref(x_7);
x_21 = lean_expr_instantiate_rev(x_18, x_6);
lean_dec_ref(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(x_3);
x_25 = lean_box(x_4);
x_26 = lean_box(x_5);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0___boxed), 17, 7);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_24);
lean_closure_set(x_27, 4, x_25);
lean_closure_set(x_27, 5, x_26);
lean_closure_set(x_27, 6, x_19);
x_28 = 0;
x_29 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(x_17, x_20, x_23, x_27, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_29;
}
else
{
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec_ref(x_7);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = 0;
x_34 = 1;
x_35 = 1;
x_36 = l_Lean_Meta_mkForallFVars(x_6, x_32, x_33, x_3, x_34, x_35, x_12, x_13, x_14, x_15);
lean_dec_ref(x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_38;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_36;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_1, x_8);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(x_2, x_3, x_4, x_5, x_6, x_18, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__2(x_1, x_2, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_22 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__1(x_1, x_2, x_18, x_19, x_20, x_21, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_1, x_2, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5(x_1, x_2, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__6(x_1, x_2, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7(x_1, x_2, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = lean_unbox(x_7);
x_22 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg(x_1, x_2, x_3, x_4, x_19, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_1);
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__8(x_18, x_2, x_3, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__1);
x_2 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___closed__2);
x_15 = l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0(lean_box(0), x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = 0;
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
x_18 = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0(x_2, x_3, x_4, x_5, x_17, x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_16);
x_21 = l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___lam__0(lean_box(0), x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_28; 
x_14 = lean_array_uget_borrowed(x_3, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_28 = lean_infer_type(x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(x_29, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__0));
x_33 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___closed__1));
x_34 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_35 = l_Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0(x_31, x_33, x_32, x_12, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = x_35;
goto block_27;
}
else
{
x_18 = x_30;
goto block_27;
}
}
else
{
x_18 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_17, x_2, x_19);
x_2 = x_21;
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_9);
x_10 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__1___redArg(x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_mkUserNameFor_spec__0___redArg___closed__1));
x_13 = 0;
x_14 = l_Lean_mkForall(x_12, x_13, x_11, x_4);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec_ref(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__3);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__4);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_72; uint8_t x_73; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
lean_dec_ref(x_10);
x_12 = lean_st_ref_get(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__2);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_2);
x_16 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_17 = lean_box(1);
x_18 = lean_box(0);
x_72 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_14, x_16, x_13, x_17, x_18);
x_73 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg(x_72, x_15);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_82; lean_object* x_83; uint8_t x_96; 
x_74 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__8));
x_75 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_74, x_6);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_96 = lean_unbox(x_76);
lean_dec(x_76);
if (x_96 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_19 = x_5;
x_20 = x_7;
x_21 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__15);
if (x_11 == 0)
{
lean_object* x_106; 
x_106 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__20));
x_98 = x_106;
goto block_105;
}
else
{
lean_object* x_107; 
x_107 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__21));
x_98 = x_107;
goto block_105;
}
block_105:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = l_Lean_stringToMessageData(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__17);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
if (x_2 == 0)
{
lean_object* x_103; 
x_103 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__18));
x_82 = x_102;
x_83 = x_103;
goto block_95;
}
else
{
lean_object* x_104; 
x_104 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__19));
x_82 = x_102;
x_83 = x_104;
goto block_95;
}
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_74, x_79, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_dec_ref(x_80);
x_19 = x_5;
x_20 = x_7;
x_21 = lean_box(0);
goto block_71;
}
else
{
lean_dec_ref(x_15);
return x_80;
}
}
block_95:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = l_Lean_stringToMessageData(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__10);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MessageData_ofName(x_1);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Name_isAnonymous(x_3);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__12);
x_92 = l_Lean_MessageData_ofName(x_3);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_77 = x_89;
x_78 = x_93;
goto block_81;
}
else
{
lean_object* x_94; 
lean_dec(x_3);
x_94 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__13);
x_77 = x_89;
x_78 = x_94;
goto block_81;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
block_71:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_st_ref_take(x_20);
x_23 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_23);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec_ref(x_23);
x_28 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_16, x_25, x_15, x_27, x_18);
lean_dec(x_27);
x_29 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5);
lean_ctor_set(x_22, 5, x_29);
lean_ctor_set(x_22, 0, x_28);
x_30 = lean_st_ref_set(x_20, x_22);
x_31 = lean_st_ref_take(x_19);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 1);
lean_dec(x_33);
x_34 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6);
lean_ctor_set(x_31, 1, x_34);
x_35 = lean_st_ref_set(x_19, x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 2);
x_40 = lean_ctor_get(x_31, 3);
x_41 = lean_ctor_get(x_31, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_42 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_st_ref_set(x_19, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
x_49 = lean_ctor_get(x_22, 2);
x_50 = lean_ctor_get(x_22, 3);
x_51 = lean_ctor_get(x_22, 4);
x_52 = lean_ctor_get(x_22, 6);
x_53 = lean_ctor_get(x_22, 7);
x_54 = lean_ctor_get(x_22, 8);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_55 = lean_ctor_get(x_23, 2);
lean_inc(x_55);
lean_dec_ref(x_23);
x_56 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_16, x_47, x_15, x_55, x_18);
lean_dec(x_55);
x_57 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__5);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_49);
lean_ctor_set(x_58, 3, x_50);
lean_ctor_set(x_58, 4, x_51);
lean_ctor_set(x_58, 5, x_57);
lean_ctor_set(x_58, 6, x_52);
lean_ctor_set(x_58, 7, x_53);
lean_ctor_set(x_58, 8, x_54);
x_59 = lean_st_ref_set(x_20, x_58);
x_60 = lean_st_ref_take(x_19);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 3);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_60, 4);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
 x_65 = lean_box(0);
}
x_66 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___closed__6);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_64);
x_68 = lean_st_ref_set(x_19, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = l_Lean_Environment_header(x_1);
x_18 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_instInhabitedEffectiveImport_default;
x_20 = lean_array_uget_borrowed(x_3, x_5);
x_21 = lean_array_get(x_19, x_18, x_20);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 0;
lean_inc(x_2);
x_25 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(x_23, x_24, x_2, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec_ref(x_25);
x_26 = lean_box(0);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_26;
goto _start;
}
else
{
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; 
x_11 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_15);
lean_dec(x_11);
x_26 = l_Lean_Environment_getModuleIdxFor_x3f(x_15, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_15);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Environment_header(x_15);
x_29 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_29);
lean_dec_ref(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_27, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec_ref(x_15);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_st_ref_get(x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__2);
x_35 = lean_array_fget(x_29, x_27);
lean_dec(x_27);
lean_dec_ref(x_29);
if (x_2 == 0)
{
lean_dec_ref(x_33);
x_36 = x_2;
goto block_47;
}
else
{
uint8_t x_48; 
lean_inc(x_1);
x_48 = l_Lean_isMarkedMeta(x_33, x_1);
if (x_48 == 0)
{
x_36 = x_2;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = 0;
x_36 = x_49;
goto block_47;
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_1);
x_39 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(x_38, x_36, x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_39);
x_40 = l_Lean_indirectModUseExt;
x_41 = lean_box(1);
x_42 = lean_box(0);
lean_inc_ref(x_15);
x_43 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_34, x_40, x_15, x_41, x_42);
x_44 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg(x_43, x_1);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___closed__3);
x_16 = lean_box(0);
x_17 = x_45;
goto block_25;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec_ref(x_44);
x_16 = lean_box(0);
x_17 = x_46;
goto block_25;
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_1);
return x_39;
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_25:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_array_size(x_17);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__15(x_15, x_1, x_17, x_19, x_20, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
}
else
{
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = 1;
x_15 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3(x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lean_box(0);
x_1 = x_13;
x_2 = x_16;
goto _start;
}
else
{
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_15, x_16);
lean_dec_ref(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_20, x_16);
lean_dec_ref(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec_ref(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_15, x_22);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_27, x_22);
lean_dec_ref(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_34, x_31);
lean_dec_ref(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec_ref(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_40, x_36);
lean_dec_ref(x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_11);
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_11, x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_free_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_12);
x_18 = l_Lean_MessageData_ofFormat(x_13);
x_19 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_11, x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_1 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_19;
}
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_12);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_11, x_25, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
x_1 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*14);
x_25 = lean_ctor_get(x_5, 12);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_27 = lean_ctor_get(x_5, 13);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_28 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_16);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_18);
lean_ctor_set(x_29, 7, x_19);
lean_ctor_set(x_29, 8, x_20);
lean_ctor_set(x_29, 9, x_21);
lean_ctor_set(x_29, 10, x_22);
lean_ctor_set(x_29, 11, x_23);
lean_ctor_set(x_29, 12, x_25);
lean_ctor_set(x_29, 13, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*14, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*14 + 1, x_26);
x_30 = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__0___redArg(x_2, x_3, x_4, x_29, x_6);
lean_dec_ref(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 10);
x_19 = lean_ctor_get(x_7, 11);
x_20 = lean_st_ref_get(x_8);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc_ref(x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_22, 0, x_11);
lean_inc_ref(x_11);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_23, 0, x_11);
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_11);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_16);
lean_closure_set(x_24, 2, x_17);
lean_inc(x_16);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_25, 0, x_16);
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_12);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_12);
lean_closure_set(x_26, 2, x_16);
lean_closure_set(x_26, 3, x_17);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_19);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_13);
lean_ctor_set(x_28, 4, x_14);
lean_ctor_set(x_28, 5, x_15);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_apply_2(x_1, x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg(x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec_ref(x_38);
x_39 = lean_st_ref_take(x_8);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 1);
lean_dec(x_41);
lean_ctor_set(x_39, 1, x_34);
x_42 = lean_st_ref_set(x_8, x_39);
x_43 = l_List_reverse___redArg(x_35);
x_44 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(x_43, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_33);
return x_44;
}
else
{
lean_object* x_47; 
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_33);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_33);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 2);
x_53 = lean_ctor_get(x_39, 3);
x_54 = lean_ctor_get(x_39, 4);
x_55 = lean_ctor_get(x_39, 5);
x_56 = lean_ctor_get(x_39, 6);
x_57 = lean_ctor_get(x_39, 7);
x_58 = lean_ctor_get(x_39, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_34);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set(x_59, 5, x_55);
lean_ctor_set(x_59, 6, x_56);
lean_ctor_set(x_59, 7, x_57);
lean_ctor_set(x_59, 8, x_58);
x_60 = lean_st_ref_set(x_8, x_59);
x_61 = l_List_reverse___redArg(x_35);
x_62 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(x_61, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_63 = x_62;
} else {
 lean_dec_ref(x_62);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_33);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_33);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_7);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
return x_38;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
lean_dec(x_38);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_31, 0);
lean_inc(x_71);
lean_dec_ref(x_31);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_73);
lean_dec_ref(x_71);
x_74 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___closed__0));
x_75 = lean_string_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(x_72, x_77, x_5, x_6, x_7, x_8);
lean_dec(x_72);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec_ref(x_73);
lean_dec_ref(x_7);
x_79 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg(x_72);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec_ref(x_7);
x_80 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___closed__2));
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMacrosInPatterns___boxed), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_2);
lean_inc_ref(x_9);
x_14 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_array_size(x_1);
x_17 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__2(x_16, x_17, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_array_size(x_15);
lean_inc(x_8);
lean_inc_ref(x_4);
lean_inc(x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__3(x_1, x_19, x_3, x_20, x_17, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_23);
x_24 = l_Lean_Elab_Do_mkMonadicType___redArg(x_23, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Array_reverse___redArg(x_19);
x_27 = lean_array_size(x_26);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg(x_26, x_27, x_17, x_25, x_8);
lean_dec(x_8);
lean_dec_ref(x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Array_unzip___redArg(x_22);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Array_unzip___redArg(x_22);
lean_dec(x_22);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_4);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___redArg(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(x_2, x_3, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; 
x_23 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_5);
x_24 = lean_unbox(x_6);
x_25 = lean_unbox(x_7);
x_26 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_23, x_24, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__5_spec__13(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__7_spec__16(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9_spec__19(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___redArg(x_1, x_2, x_3, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__4_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__21(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__23___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__16_spec__29(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__0_spec__0_spec__10_spec__22_spec__27_spec__31___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__3_spec__14_spec__26_spec__31_spec__35(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), x_1, x_2, x_14, x_4, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_11, x_12, x_11, x_12, x_13, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_9 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = l_Lean_Syntax_getId(x_17);
lean_dec(x_17);
lean_ctor_set(x_6, 0, x_18);
x_9 = x_6;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_Syntax_getId(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_9 = x_21;
goto block_14;
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__0));
x_14 = l_Lean_Elab_Term_mkAuxName(x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_array_size(x_1);
x_18 = 0;
lean_inc_ref(x_1);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__0(x_17, x_18, x_1);
x_20 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_3);
lean_ctor_set(x_21, 4, x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_22 = l_Lean_Meta_Match_mkMatcher(x_21, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_reportMatcherResultErrors(x_3, x_23, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_26);
lean_dec(x_23);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = lean_apply_5(x_26, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec_ref(x_27);
x_28 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__1));
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_30 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_31 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__1___redArg(x_2, x_29, x_28, x_30, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_34 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_33, x_10);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_Expr_app___override(x_25, x_32);
x_38 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2(x_17, x_18, x_1);
x_39 = l_Lean_mkAppN(x_37, x_38);
lean_dec_ref(x_38);
x_40 = l_Lean_mkAppN(x_39, x_4);
x_41 = lean_unbox(x_36);
lean_dec(x_36);
if (x_41 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_34);
x_42 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3);
lean_inc_ref(x_40);
x_43 = l_Lean_MessageData_ofExpr(x_40);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_33, x_44, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_40);
return x_45;
}
else
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_40);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_40);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
x_53 = l_Lean_Expr_app___override(x_25, x_32);
x_54 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch_spec__2(x_17, x_18, x_1);
x_55 = l_Lean_mkAppN(x_53, x_54);
lean_dec_ref(x_54);
x_56 = l_Lean_mkAppN(x_55, x_4);
x_57 = lean_unbox(x_52);
lean_dec(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___closed__3);
lean_inc_ref(x_56);
x_60 = l_Lean_MessageData_ofExpr(x_56);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_33, x_61, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_63 = x_62;
} else {
 lean_dec_ref(x_62);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_56);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
}
else
{
lean_dec_ref(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_31;
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_27);
if (x_68 == 0)
{
return x_27;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_27, 0);
lean_inc(x_69);
lean_dec(x_27);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_24, 0);
lean_inc(x_72);
lean_dec(x_24);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_22);
if (x_74 == 0)
{
return x_22;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
lean_dec(x_22);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
return x_14;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_14, 0);
lean_inc(x_78);
lean_dec(x_14);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_14);
x_15 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_23 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l_Lean_Elab_Term_instantiateAltLHSs(x_21, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_18, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_18, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_16);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_16);
lean_dec(x_20);
lean_dec(x_14);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_18);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_16);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_40 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
x_41 = l_Lean_Elab_Term_instantiateAltLHSs(x_38, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_16, 1, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_16);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_free_object(x_16);
lean_dec(x_37);
lean_dec(x_14);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_16);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_16, 1);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_58 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec_ref(x_58);
x_59 = l_Lean_Elab_Term_instantiateAltLHSs(x_55, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_14);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_70 = x_58;
} else {
 lean_dec_ref(x_58);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_72 = !lean_is_exclusive(x_15);
if (x_72 == 0)
{
return x_15;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_15, 0);
lean_inc(x_73);
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_75 = !lean_is_exclusive(x_13);
if (x_75 == 0)
{
return x_13;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_13, 0);
lean_inc(x_76);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__3));
x_43 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__3___redArg(x_42, x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_unbox(x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec_ref(x_4);
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_47);
lean_dec_ref(x_4);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
x_49 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__1);
lean_inc_ref(x_1);
x_50 = lean_array_to_list(x_1);
x_51 = lean_box(0);
x_52 = l_List_mapTR_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__2(x_50, x_51);
x_53 = l_Lean_MessageData_ofList(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__3);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_47);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___closed__5);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
if (x_48 == 0)
{
lean_object* x_70; 
x_70 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__12));
x_61 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__13));
x_61 = x_71;
goto block_69;
}
block_69:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_45)) {
 x_62 = lean_alloc_ctor(3, 1, 0);
} else {
 x_62 = x_45;
 lean_ctor_set_tag(x_62, 3);
}
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_MessageData_ofFormat(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType_spec__4___redArg(x_42, x_64, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = lean_box(0);
goto block_41;
}
else
{
uint8_t x_66; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
block_41:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_22 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar(x_1, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec_ref(x_1);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_inc_ref(x_14);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__1___boxed), 12, 5);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_5);
lean_closure_set(x_25, 4, x_14);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_26 = l_Lean_Elab_Term_commitIfDidNotPostpone___redArg(x_25, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_compileMatch(x_30, x_31, x_32, x_33, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_uget_borrowed(x_1, x_2);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_20);
x_21 = l_Lean_Elab_Do_inferControlInfoSeq(x_20, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Elab_Do_ControlInfo_alternative(x_4, x_22);
x_12 = x_23;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_12 = x_24;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_21;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__0___boxed), 8, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___lam__2___boxed), 13, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
x_21 = l_Lean_Elab_Do_ControlInfo_pure;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_2);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_2);
x_25 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_3, x_21, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
if (x_24 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_2);
x_27 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_3, x_21, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_23);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(x_2, x_28, x_29, x_21, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
x_14 = x_30;
goto block_20;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_23);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(x_2, x_31, x_32, x_21, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
x_14 = x_33;
goto block_20;
}
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(x_3, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = 1;
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___closed__1));
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Syntax_isQuot(x_11);
x_6 = x_14;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_11, x_15);
x_18 = l_Lean_Syntax_matchesNull(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Syntax_isQuot(x_11);
x_6 = x_19;
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_11, x_20);
x_22 = l_Lean_Syntax_isQuot(x_21);
lean_dec(x_21);
x_6 = x_22;
goto block_10;
}
}
block_10:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = 1;
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19));
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
x_6 = x_13;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_11, x_14);
lean_inc(x_15);
x_16 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_15);
x_6 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_15, x_17);
lean_dec(x_15);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = l_Lean_Syntax_TSepArray_getElems___redArg(x_19);
lean_dec_ref(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_17, x_21);
if (x_22 == 0)
{
lean_dec_ref(x_20);
x_6 = x_4;
goto block_10;
}
else
{
if (x_22 == 0)
{
lean_dec_ref(x_20);
x_6 = x_4;
goto block_10;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_21);
x_25 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__0(x_20, x_23, x_24);
lean_dec_ref(x_20);
x_6 = x_25;
goto block_10;
}
}
}
}
block_10:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Do_isSyntaxMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_4;
}
else
{
if (x_4 == 0)
{
return x_4;
}
else
{
size_t x_5; size_t x_6; uint8_t x_7; 
x_5 = 0;
x_6 = lean_usize_of_nat(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Do_isSyntaxMatch_spec__1(x_1, x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isSyntaxMatch___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Do_isSyntaxMatch(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_uget_borrowed(x_1, x_3);
x_21 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19));
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_20, x_27);
lean_inc(x_28);
x_29 = l_Lean_Syntax_matchesNull(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_tryPostponeIfDiscrTypeIsMVar_spec__0___redArg();
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_28, x_34);
lean_dec(x_28);
x_36 = l_Lean_Syntax_getArgs(x_35);
lean_dec(x_35);
x_37 = l_Lean_Syntax_TSepArray_getElems___redArg(x_36);
lean_dec_ref(x_36);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_38 = l_Lean_Elab_Do_getPatternsVarsEx(x_37, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Array_append___redArg(x_4, x_39);
lean_dec(x_39);
x_12 = x_40;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_38;
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getAltsPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f___closed__0);
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_getAltsPatternVars_spec__0(x_1, x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_getAltsPatternVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_getAltsPatternVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_11);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_2);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_1);
x_12 = lean_ctor_get(x_11, 7);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
lean_inc(x_1);
x_14 = lean_apply_8(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_1, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_take(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 2);
lean_dec(x_21);
x_22 = l_Lean_PersistentArray_push___redArg(x_8, x_16);
lean_ctor_set(x_19, 2, x_22);
x_23 = lean_st_ref_set(x_1, x_17);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = l_Lean_PersistentArray_push___redArg(x_8, x_16);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_25);
lean_ctor_set(x_17, 7, x_29);
x_30 = lean_st_ref_set(x_1, x_17);
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_17, 7);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
x_35 = lean_ctor_get(x_17, 2);
x_36 = lean_ctor_get(x_17, 3);
x_37 = lean_ctor_get(x_17, 4);
x_38 = lean_ctor_get(x_17, 5);
x_39 = lean_ctor_get(x_17, 6);
x_40 = lean_ctor_get(x_17, 8);
lean_inc(x_40);
lean_inc(x_32);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_41 = lean_ctor_get_uint8(x_32, sizeof(void*)*3);
x_42 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_44 = x_32;
} else {
 lean_dec_ref(x_32);
 x_44 = lean_box(0);
}
x_45 = l_Lean_PersistentArray_push___redArg(x_8, x_16);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 3, 1);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_41);
x_47 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_36);
lean_ctor_set(x_47, 4, x_37);
lean_ctor_set(x_47, 5, x_38);
lean_ctor_set(x_47, 6, x_39);
lean_ctor_set(x_47, 7, x_46);
lean_ctor_set(x_47, 8, x_40);
x_48 = lean_st_ref_set(x_1, x_47);
lean_dec(x_1);
x_49 = lean_box(0);
lean_ctor_set(x_14, 0, x_49);
return x_14;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_st_ref_take(x_1);
x_52 = lean_ctor_get(x_51, 7);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_51, 4);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_51, 5);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_51, 6);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_51, 8);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 lean_ctor_release(x_51, 6);
 lean_ctor_release(x_51, 7);
 lean_ctor_release(x_51, 8);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get_uint8(x_52, sizeof(void*)*3);
x_63 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 x_65 = x_52;
} else {
 lean_dec_ref(x_52);
 x_65 = lean_box(0);
}
x_66 = l_Lean_PersistentArray_push___redArg(x_8, x_50);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 3, 1);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_62);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 9, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_54);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_56);
lean_ctor_set(x_68, 4, x_57);
lean_ctor_set(x_68, 5, x_58);
lean_ctor_set(x_68, 6, x_59);
lean_ctor_set(x_68, 7, x_67);
lean_ctor_set(x_68, 8, x_60);
x_69 = lean_st_ref_set(x_1, x_68);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec_ref(x_8);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_14);
if (x_72 == 0)
{
return x_14;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_14, 0);
lean_inc(x_73);
lean_dec(x_14);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
x_4 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
x_11 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2);
lean_ctor_set(x_8, 2, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
lean_ctor_set(x_6, 7, x_18);
x_19 = lean_st_ref_set(x_1, x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_6, 7);
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
x_24 = lean_ctor_get(x_6, 2);
x_25 = lean_ctor_get(x_6, 3);
x_26 = lean_ctor_get(x_6, 4);
x_27 = lean_ctor_get(x_6, 5);
x_28 = lean_ctor_get(x_6, 6);
x_29 = lean_ctor_get(x_6, 8);
lean_inc(x_29);
lean_inc(x_21);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___closed__2);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_30);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set(x_36, 4, x_26);
lean_ctor_set(x_36, 5, x_27);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_29);
x_37 = lean_st_ref_set(x_1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 7);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec_ref(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_2);
x_13 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_ctor_set_tag(x_16, 1);
x_19 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_16);
lean_dec_ref(x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_27);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_29 = x_28;
} else {
 lean_dec_ref(x_28);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec_ref(x_16);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; 
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_34);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg(x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg(x_1, x_2, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_getMatchAlt___redArg(x_11);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_array_push(x_4, x_13);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_obj_once(&l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0, &l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0_once, _init_l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___closed__0);
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1_spec__2(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoMatch___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoMatch___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9));
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_47; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_388; uint8_t x_389; 
x_48 = lean_unsigned_to_nat(0u);
x_211 = lean_unsigned_to_nat(1u);
x_388 = l_Lean_Syntax_getArg(x_1, x_211);
x_389 = l_Lean_Syntax_isNone(x_388);
if (x_389 == 0)
{
uint8_t x_390; 
lean_inc(x_388);
x_390 = l_Lean_Syntax_matchesNull(x_388, x_211);
if (x_390 == 0)
{
lean_object* x_391; 
lean_dec(x_388);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_391 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_392 = l_Lean_Syntax_getArg(x_388, x_48);
lean_dec(x_388);
x_393 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__17));
lean_inc(x_392);
x_394 = l_Lean_Syntax_isOfKind(x_392, x_393);
if (x_394 == 0)
{
lean_object* x_395; 
lean_dec(x_392);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_395 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_unsigned_to_nat(3u);
x_397 = l_Lean_Syntax_getArg(x_392, x_396);
lean_dec(x_392);
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_397);
x_365 = x_398;
x_366 = x_3;
x_367 = x_4;
x_368 = x_5;
x_369 = x_6;
x_370 = x_7;
x_371 = x_8;
x_372 = x_9;
x_373 = lean_box(0);
goto block_387;
}
}
}
else
{
lean_object* x_399; 
lean_dec(x_388);
x_399 = lean_box(0);
x_365 = x_399;
x_366 = x_3;
x_367 = x_4;
x_368 = x_5;
x_369 = x_6;
x_370 = x_7;
x_371 = x_8;
x_372 = x_9;
x_373 = lean_box(0);
goto block_387;
}
block_71:
{
lean_object* x_59; 
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
x_59 = l_Lean_Elab_Do_getAltsPatternVars(x_49, x_52, x_53, x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_56);
x_61 = l_Lean_Elab_Do_checkMutVarsForShadowing(x_60, x_51, x_52, x_53, x_54, x_55, x_56, x_57);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_61);
x_62 = lean_array_get_size(x_49);
x_63 = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoMatch_spec__1(x_49, x_48, x_62);
lean_dec_ref(x_49);
x_64 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoMatchCore(x_50, x_63, x_2, x_51, x_52, x_53, x_54, x_55, x_56, x_57);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_2);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
block_89:
{
if (lean_obj_tag(x_72) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_2);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
lean_dec_ref(x_72);
x_84 = lean_obj_once(&l_Lean_Elab_Do_elabDoMatch___closed__1, &l_Lean_Elab_Do_elabDoMatch___closed__1_once, _init_l_Lean_Elab_Do_elabDoMatch___closed__1);
x_85 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(x_83, x_84, x_78, x_79, x_80, x_81);
lean_dec(x_81);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
lean_dec(x_72);
x_49 = x_73;
x_50 = x_74;
x_51 = x_75;
x_52 = x_76;
x_53 = x_77;
x_54 = x_78;
x_55 = x_79;
x_56 = x_80;
x_57 = x_81;
x_58 = lean_box(0);
goto block_71;
}
}
block_114:
{
lean_object* x_104; uint8_t x_105; 
x_104 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__15));
x_105 = l_Lean_Syntax_isOfKind(x_103, x_104);
if (x_105 == 0)
{
if (x_95 == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_94);
lean_dec_ref(x_91);
lean_dec_ref(x_2);
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec_ref(x_101);
x_107 = lean_obj_once(&l_Lean_Elab_Do_elabDoMatch___closed__3, &l_Lean_Elab_Do_elabDoMatch___closed__3_once, _init_l_Lean_Elab_Do_elabDoMatch___closed__3);
x_108 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1_spec__6___redArg(x_106, x_107, x_93, x_102, x_92, x_96);
lean_dec(x_96);
lean_dec(x_102);
lean_dec_ref(x_93);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
else
{
lean_dec(x_101);
x_72 = x_99;
x_73 = x_91;
x_74 = x_100;
x_75 = x_97;
x_76 = x_94;
x_77 = x_98;
x_78 = x_93;
x_79 = x_102;
x_80 = x_92;
x_81 = x_96;
x_82 = lean_box(0);
goto block_89;
}
}
else
{
lean_object* x_112; 
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_91);
x_112 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(x_1, x_2, x_97, x_94, x_98, x_93, x_102, x_92, x_96);
return x_112;
}
}
else
{
lean_object* x_113; 
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_91);
x_113 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(x_1, x_2, x_97, x_94, x_98, x_93, x_102, x_92, x_96);
return x_113;
}
}
block_132:
{
uint8_t x_128; 
x_128 = l_Lean_Elab_Do_isSyntaxMatch(x_117);
if (x_128 == 0)
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_129; 
x_129 = lean_box(0);
x_90 = lean_box(0);
x_91 = x_117;
x_92 = x_125;
x_93 = x_123;
x_94 = x_121;
x_95 = x_128;
x_96 = x_126;
x_97 = x_120;
x_98 = x_122;
x_99 = x_116;
x_100 = x_118;
x_101 = x_119;
x_102 = x_124;
x_103 = x_129;
goto block_114;
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_115, 0);
lean_inc(x_130);
lean_dec_ref(x_115);
x_90 = lean_box(0);
x_91 = x_117;
x_92 = x_125;
x_93 = x_123;
x_94 = x_121;
x_95 = x_128;
x_96 = x_126;
x_97 = x_120;
x_98 = x_122;
x_99 = x_116;
x_100 = x_118;
x_101 = x_119;
x_102 = x_124;
x_103 = x_130;
goto block_114;
}
}
else
{
lean_object* x_131; 
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_131 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch(x_1, x_2, x_120, x_121, x_122, x_123, x_124, x_125, x_126);
return x_131;
}
}
block_184:
{
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec(x_138);
lean_dec(x_136);
x_115 = x_141;
x_116 = x_142;
x_117 = x_135;
x_118 = x_144;
x_119 = x_146;
x_120 = x_134;
x_121 = x_148;
x_122 = x_133;
x_123 = x_137;
x_124 = x_145;
x_125 = x_139;
x_126 = x_140;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_146);
lean_dec_ref(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec_ref(x_135);
x_150 = lean_ctor_get(x_139, 5);
x_151 = 0;
x_152 = l_Lean_SourceInfo_fromRef(x_150, x_151);
x_153 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__5));
x_154 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2));
x_155 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__7));
x_156 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__9));
x_157 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__10));
lean_inc(x_152);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3);
lean_inc(x_152);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_152);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set(x_160, 2, x_159);
x_161 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__12));
x_162 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__14));
x_163 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__16));
lean_inc(x_152);
x_164 = l_Lean_Syntax_node1(x_152, x_163, x_136);
x_165 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12));
lean_inc(x_152);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_152);
lean_ctor_set(x_166, 1, x_165);
lean_inc_ref_n(x_160, 2);
lean_inc(x_152);
x_167 = l_Lean_Syntax_node5(x_152, x_162, x_164, x_160, x_160, x_166, x_138);
lean_inc(x_152);
x_168 = l_Lean_Syntax_node1(x_152, x_161, x_167);
lean_inc_ref(x_160);
lean_inc(x_152);
x_169 = l_Lean_Syntax_node3(x_152, x_156, x_158, x_160, x_168);
x_170 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__17));
lean_inc(x_152);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_152);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_152);
x_172 = l_Lean_Syntax_node1(x_152, x_154, x_171);
lean_inc(x_152);
x_173 = l_Lean_Syntax_node2(x_152, x_155, x_169, x_172);
x_174 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__19));
x_175 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__1));
lean_inc(x_152);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_152);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_152);
x_177 = l_Lean_Syntax_node2(x_152, x_174, x_176, x_147);
lean_inc(x_152);
x_178 = l_Lean_Syntax_node2(x_152, x_155, x_177, x_160);
lean_inc(x_152);
x_179 = l_Lean_Syntax_node2(x_152, x_154, x_173, x_178);
x_180 = l_Lean_Syntax_node1(x_152, x_153, x_179);
x_181 = lean_box(x_12);
lean_inc(x_180);
x_182 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(x_182, 0, x_180);
lean_closure_set(x_182, 1, x_2);
lean_closure_set(x_182, 2, x_181);
x_183 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(x_1, x_180, x_182, x_134, x_148, x_133, x_137, x_145, x_139, x_140);
return x_183;
}
}
block_210:
{
lean_object* x_204; lean_object* x_205; 
lean_inc_ref(x_196);
x_204 = l_Array_append___redArg(x_196, x_203);
lean_dec_ref(x_203);
lean_inc(x_193);
lean_inc(x_197);
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_197);
lean_ctor_set(x_205, 1, x_193);
lean_ctor_set(x_205, 2, x_204);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_206; 
x_206 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_13 = x_185;
x_14 = x_186;
x_15 = x_187;
x_16 = x_188;
x_17 = x_189;
x_18 = x_205;
x_19 = x_190;
x_20 = x_191;
x_21 = x_192;
x_22 = x_193;
x_23 = lean_box(0);
x_24 = x_195;
x_25 = x_196;
x_26 = x_197;
x_27 = x_200;
x_28 = x_199;
x_29 = x_201;
x_30 = x_202;
x_31 = x_206;
goto block_46;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_198, 0);
lean_inc(x_207);
lean_dec_ref(x_198);
x_208 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_209 = lean_array_push(x_208, x_207);
x_13 = x_185;
x_14 = x_186;
x_15 = x_187;
x_16 = x_188;
x_17 = x_189;
x_18 = x_205;
x_19 = x_190;
x_20 = x_191;
x_21 = x_192;
x_22 = x_193;
x_23 = lean_box(0);
x_24 = x_195;
x_25 = x_196;
x_26 = x_197;
x_27 = x_200;
x_28 = x_199;
x_29 = x_201;
x_30 = x_202;
x_31 = x_209;
goto block_46;
}
}
block_241:
{
uint8_t x_229; 
lean_inc(x_228);
x_229 = l_Lean_Syntax_isOfKind(x_228, x_212);
lean_dec(x_212);
if (x_229 == 0)
{
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_216);
x_115 = x_220;
x_116 = x_222;
x_117 = x_215;
x_118 = x_223;
x_119 = x_224;
x_120 = x_214;
x_121 = x_227;
x_122 = x_213;
x_123 = x_217;
x_124 = x_225;
x_125 = x_218;
x_126 = x_219;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_230; uint8_t x_231; 
x_230 = l_Lean_Syntax_getArg(x_228, x_48);
x_231 = l_Lean_Syntax_matchesNull(x_230, x_48);
if (x_231 == 0)
{
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_216);
x_115 = x_220;
x_116 = x_222;
x_117 = x_215;
x_118 = x_223;
x_119 = x_224;
x_120 = x_214;
x_121 = x_227;
x_122 = x_213;
x_123 = x_217;
x_124 = x_225;
x_125 = x_218;
x_126 = x_219;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_232; 
lean_inc(x_219);
lean_inc_ref(x_218);
lean_inc(x_225);
lean_inc_ref(x_217);
lean_inc(x_213);
lean_inc_ref(x_227);
lean_inc(x_216);
x_232 = l_Lean_Elab_Term_isPatternVar(x_216, x_227, x_213, x_217, x_225, x_218, x_219);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = l_Lean_Syntax_getArg(x_228, x_211);
lean_dec(x_228);
x_235 = lean_array_get_size(x_215);
x_236 = lean_nat_dec_eq(x_235, x_211);
if (x_236 == 0)
{
lean_dec(x_233);
x_133 = x_213;
x_134 = x_214;
x_135 = x_215;
x_136 = x_216;
x_137 = x_217;
x_138 = x_234;
x_139 = x_218;
x_140 = x_219;
x_141 = x_220;
x_142 = x_222;
x_143 = lean_box(0);
x_144 = x_223;
x_145 = x_225;
x_146 = x_224;
x_147 = x_226;
x_148 = x_227;
x_149 = x_236;
goto block_184;
}
else
{
uint8_t x_237; 
x_237 = lean_unbox(x_233);
lean_dec(x_233);
x_133 = x_213;
x_134 = x_214;
x_135 = x_215;
x_136 = x_216;
x_137 = x_217;
x_138 = x_234;
x_139 = x_218;
x_140 = x_219;
x_141 = x_220;
x_142 = x_222;
x_143 = lean_box(0);
x_144 = x_223;
x_145 = x_225;
x_146 = x_224;
x_147 = x_226;
x_148 = x_227;
x_149 = x_237;
goto block_184;
}
}
else
{
uint8_t x_238; 
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_219);
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_232);
if (x_238 == 0)
{
return x_232;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_232, 0);
lean_inc(x_239);
lean_dec(x_232);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
}
}
}
}
block_272:
{
uint8_t x_260; 
lean_inc(x_259);
x_260 = l_Lean_Syntax_isOfKind(x_259, x_244);
lean_dec(x_244);
if (x_260 == 0)
{
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_242);
x_115 = x_250;
x_116 = x_252;
x_117 = x_246;
x_118 = x_253;
x_119 = x_254;
x_120 = x_245;
x_121 = x_257;
x_122 = x_243;
x_123 = x_247;
x_124 = x_255;
x_125 = x_248;
x_126 = x_249;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = l_Lean_Syntax_getArg(x_259, x_211);
lean_inc(x_261);
x_262 = l_Lean_Syntax_matchesNull(x_261, x_211);
if (x_262 == 0)
{
lean_dec(x_261);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_242);
x_115 = x_250;
x_116 = x_252;
x_117 = x_246;
x_118 = x_253;
x_119 = x_254;
x_120 = x_245;
x_121 = x_257;
x_122 = x_243;
x_123 = x_247;
x_124 = x_255;
x_125 = x_248;
x_126 = x_249;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_263; uint8_t x_264; 
x_263 = l_Lean_Syntax_getArg(x_261, x_48);
lean_dec(x_261);
lean_inc(x_263);
x_264 = l_Lean_Syntax_matchesNull(x_263, x_211);
if (x_264 == 0)
{
lean_dec(x_263);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_242);
x_115 = x_250;
x_116 = x_252;
x_117 = x_246;
x_118 = x_253;
x_119 = x_254;
x_120 = x_245;
x_121 = x_257;
x_122 = x_243;
x_123 = x_247;
x_124 = x_255;
x_125 = x_248;
x_126 = x_249;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = l_Lean_Syntax_getArg(x_263, x_48);
lean_dec(x_263);
x_266 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___closed__21));
lean_inc(x_265);
x_267 = l_Lean_Syntax_isOfKind(x_265, x_266);
if (x_267 == 0)
{
lean_dec(x_265);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_242);
x_115 = x_250;
x_116 = x_252;
x_117 = x_246;
x_118 = x_253;
x_119 = x_254;
x_120 = x_245;
x_121 = x_257;
x_122 = x_243;
x_123 = x_247;
x_124 = x_255;
x_125 = x_248;
x_126 = x_249;
x_127 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = l_Lean_Syntax_getArg(x_259, x_256);
lean_dec(x_259);
x_269 = lean_array_get_size(x_253);
x_270 = lean_nat_dec_lt(x_48, x_269);
if (x_270 == 0)
{
x_212 = x_242;
x_213 = x_243;
x_214 = x_245;
x_215 = x_246;
x_216 = x_265;
x_217 = x_247;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = lean_box(0);
x_222 = x_252;
x_223 = x_253;
x_224 = x_254;
x_225 = x_255;
x_226 = x_268;
x_227 = x_257;
x_228 = x_258;
goto block_241;
}
else
{
lean_object* x_271; 
lean_dec(x_258);
x_271 = lean_array_fget(x_253, x_48);
x_212 = x_242;
x_213 = x_243;
x_214 = x_245;
x_215 = x_246;
x_216 = x_265;
x_217 = x_247;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = lean_box(0);
x_222 = x_252;
x_223 = x_253;
x_224 = x_254;
x_225 = x_255;
x_226 = x_268;
x_227 = x_257;
x_228 = x_271;
goto block_241;
}
}
}
}
}
}
block_333:
{
lean_object* x_291; lean_object* x_292; 
lean_inc(x_1);
x_291 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAlts_x3f___boxed), 3, 1);
lean_closure_set(x_291, 0, x_1);
lean_inc_ref(x_280);
x_292 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabMatchAlts_spec__1___redArg(x_291, x_276, x_289, x_274, x_279, x_287, x_280, x_281);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
if (lean_obj_tag(x_293) == 1)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_290);
lean_dec_ref(x_286);
lean_dec(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_278);
lean_dec_ref(x_277);
lean_dec(x_275);
lean_dec(x_273);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec_ref(x_293);
x_295 = lean_box(x_12);
lean_inc(x_294);
x_296 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(x_296, 0, x_294);
lean_closure_set(x_296, 1, x_2);
lean_closure_set(x_296, 2, x_295);
x_297 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(x_1, x_294, x_296, x_276, x_289, x_274, x_279, x_287, x_280, x_281);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_293);
x_298 = l_Lean_Syntax_TSepArray_getElems___redArg(x_282);
lean_dec_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_287);
lean_inc_ref(x_279);
lean_inc(x_274);
lean_inc_ref(x_289);
x_299 = l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f(x_298, x_276, x_289, x_274, x_279, x_287, x_280, x_281);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
if (lean_obj_tag(x_300) == 1)
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_298);
lean_dec(x_283);
lean_dec(x_275);
lean_dec(x_273);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
lean_dec_ref(x_300);
x_302 = lean_ctor_get(x_280, 5);
x_303 = 0;
x_304 = l_Lean_SourceInfo_fromRef(x_302, x_303);
x_305 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_elabDoSeqWithRefinedType___closed__2));
lean_inc(x_304);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__2));
x_308 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___lam__0___closed__3);
lean_inc(x_304);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_304);
lean_ctor_set(x_309, 1, x_307);
lean_ctor_set(x_309, 2, x_308);
if (lean_obj_tag(x_284) == 1)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_310 = lean_ctor_get(x_284, 0);
lean_inc(x_310);
lean_dec_ref(x_284);
x_311 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16));
x_312 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__11));
lean_inc(x_304);
x_313 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_313, 0, x_304);
lean_ctor_set(x_313, 1, x_312);
x_314 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__17));
lean_inc(x_304);
x_315 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_315, 0, x_304);
lean_ctor_set(x_315, 1, x_314);
x_316 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__12));
lean_inc(x_304);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_304);
lean_ctor_set(x_317, 1, x_316);
x_318 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__13));
lean_inc(x_304);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_304);
lean_ctor_set(x_319, 1, x_318);
lean_inc(x_304);
x_320 = l_Lean_Syntax_node5(x_304, x_311, x_313, x_315, x_317, x_310, x_319);
x_321 = l_Array_mkArray1___redArg(x_320);
x_185 = x_309;
x_186 = x_274;
x_187 = x_276;
x_188 = x_277;
x_189 = x_278;
x_190 = x_279;
x_191 = x_280;
x_192 = x_281;
x_193 = x_307;
x_194 = lean_box(0);
x_195 = x_306;
x_196 = x_308;
x_197 = x_304;
x_198 = x_290;
x_199 = x_286;
x_200 = x_287;
x_201 = x_301;
x_202 = x_289;
x_203 = x_321;
goto block_210;
}
else
{
lean_object* x_322; 
lean_dec(x_284);
x_322 = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14, &l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14_once, _init_l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__14);
x_185 = x_309;
x_186 = x_274;
x_187 = x_276;
x_188 = x_277;
x_189 = x_278;
x_190 = x_279;
x_191 = x_280;
x_192 = x_281;
x_193 = x_307;
x_194 = lean_box(0);
x_195 = x_306;
x_196 = x_308;
x_197 = x_304;
x_198 = x_290;
x_199 = x_286;
x_200 = x_287;
x_201 = x_301;
x_202 = x_289;
x_203 = x_322;
goto block_210;
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; 
lean_dec(x_300);
lean_dec_ref(x_286);
lean_dec(x_278);
x_323 = lean_box(0);
x_324 = lean_array_get_size(x_277);
x_325 = lean_nat_dec_lt(x_48, x_324);
if (x_325 == 0)
{
x_242 = x_273;
x_243 = x_274;
x_244 = x_275;
x_245 = x_276;
x_246 = x_277;
x_247 = x_279;
x_248 = x_280;
x_249 = x_281;
x_250 = x_283;
x_251 = lean_box(0);
x_252 = x_284;
x_253 = x_298;
x_254 = x_290;
x_255 = x_287;
x_256 = x_288;
x_257 = x_289;
x_258 = x_323;
x_259 = x_323;
goto block_272;
}
else
{
lean_object* x_326; 
x_326 = lean_array_fget(x_277, x_48);
x_242 = x_273;
x_243 = x_274;
x_244 = x_275;
x_245 = x_276;
x_246 = x_277;
x_247 = x_279;
x_248 = x_280;
x_249 = x_281;
x_250 = x_283;
x_251 = lean_box(0);
x_252 = x_284;
x_253 = x_298;
x_254 = x_290;
x_255 = x_287;
x_256 = x_288;
x_257 = x_289;
x_258 = x_323;
x_259 = x_326;
goto block_272;
}
}
}
else
{
uint8_t x_327; 
lean_dec_ref(x_298);
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_2);
lean_dec(x_1);
x_327 = !lean_is_exclusive(x_299);
if (x_327 == 0)
{
return x_299;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_299, 0);
lean_inc(x_328);
lean_dec(x_299);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_290);
lean_dec_ref(x_289);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_2);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_292);
if (x_330 == 0)
{
return x_292;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_292, 0);
lean_inc(x_331);
lean_dec(x_292);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
}
}
block_364:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_344 = lean_unsigned_to_nat(6u);
x_345 = l_Lean_Syntax_getArg(x_1, x_344);
x_346 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__8));
lean_inc(x_345);
x_347 = l_Lean_Syntax_isOfKind(x_345, x_346);
if (x_347 == 0)
{
lean_object* x_348; 
lean_dec(x_345);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec_ref(x_337);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec_ref(x_2);
lean_dec(x_1);
x_348 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_349 = lean_unsigned_to_nat(3u);
x_350 = l_Lean_Syntax_getArg(x_1, x_349);
x_351 = lean_unsigned_to_nat(4u);
x_352 = l_Lean_Syntax_getArg(x_1, x_351);
x_353 = l_Lean_Syntax_getArg(x_345, x_48);
lean_dec(x_345);
x_354 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__19));
x_355 = l_Lean_Syntax_getArgs(x_353);
lean_dec(x_353);
x_356 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandNonAtomicDiscrs_x3f_spec__0___redArg___closed__1));
x_357 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__4));
x_358 = l_Lean_Syntax_getArgs(x_352);
lean_dec(x_352);
x_359 = l_Lean_Syntax_getOptional_x3f(x_350);
lean_dec(x_350);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; 
x_360 = lean_box(0);
x_273 = x_356;
x_274 = x_338;
x_275 = x_354;
x_276 = x_336;
x_277 = x_355;
x_278 = x_346;
x_279 = x_339;
x_280 = x_341;
x_281 = x_342;
x_282 = x_358;
x_283 = x_334;
x_284 = x_335;
x_285 = lean_box(0);
x_286 = x_357;
x_287 = x_340;
x_288 = x_349;
x_289 = x_337;
x_290 = x_360;
goto block_333;
}
else
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_359);
if (x_361 == 0)
{
x_273 = x_356;
x_274 = x_338;
x_275 = x_354;
x_276 = x_336;
x_277 = x_355;
x_278 = x_346;
x_279 = x_339;
x_280 = x_341;
x_281 = x_342;
x_282 = x_358;
x_283 = x_334;
x_284 = x_335;
x_285 = lean_box(0);
x_286 = x_357;
x_287 = x_340;
x_288 = x_349;
x_289 = x_337;
x_290 = x_359;
goto block_333;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_273 = x_356;
x_274 = x_338;
x_275 = x_354;
x_276 = x_336;
x_277 = x_355;
x_278 = x_346;
x_279 = x_339;
x_280 = x_341;
x_281 = x_342;
x_282 = x_358;
x_283 = x_334;
x_284 = x_335;
x_285 = lean_box(0);
x_286 = x_357;
x_287 = x_340;
x_288 = x_349;
x_289 = x_337;
x_290 = x_363;
goto block_333;
}
}
}
}
block_387:
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_unsigned_to_nat(2u);
x_375 = l_Lean_Syntax_getArg(x_1, x_374);
x_376 = l_Lean_Syntax_isNone(x_375);
if (x_376 == 0)
{
uint8_t x_377; 
lean_inc(x_375);
x_377 = l_Lean_Syntax_matchesNull(x_375, x_211);
if (x_377 == 0)
{
lean_object* x_378; 
lean_dec(x_375);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_2);
lean_dec(x_1);
x_378 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = l_Lean_Syntax_getArg(x_375, x_48);
lean_dec(x_375);
x_380 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__16));
lean_inc(x_379);
x_381 = l_Lean_Syntax_isOfKind(x_379, x_380);
if (x_381 == 0)
{
lean_object* x_382; 
lean_dec(x_379);
lean_dec(x_372);
lean_dec_ref(x_371);
lean_dec(x_370);
lean_dec_ref(x_369);
lean_dec(x_368);
lean_dec_ref(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_2);
lean_dec(x_1);
x_382 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop_spec__1___redArg();
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_unsigned_to_nat(3u);
x_384 = l_Lean_Syntax_getArg(x_379, x_383);
lean_dec(x_379);
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_334 = x_365;
x_335 = x_385;
x_336 = x_366;
x_337 = x_367;
x_338 = x_368;
x_339 = x_369;
x_340 = x_370;
x_341 = x_371;
x_342 = x_372;
x_343 = lean_box(0);
goto block_364;
}
}
}
else
{
lean_object* x_386; 
lean_dec(x_375);
x_386 = lean_box(0);
x_334 = x_365;
x_335 = x_386;
x_336 = x_366;
x_337 = x_367;
x_338 = x_368;
x_339 = x_369;
x_340 = x_370;
x_341 = x_371;
x_342 = x_372;
x_343 = lean_box(0);
goto block_364;
}
}
}
block_46:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc_ref(x_25);
x_32 = l_Array_append___redArg(x_25, x_31);
lean_dec_ref(x_31);
lean_inc(x_22);
lean_inc(x_26);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_Lean_Syntax_SepArray_ofElems(x_28, x_29);
lean_dec_ref(x_29);
lean_inc_ref(x_25);
x_35 = l_Array_append___redArg(x_25, x_34);
lean_dec_ref(x_34);
lean_inc(x_22);
lean_inc(x_26);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_35);
x_37 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch_loop___closed__6));
lean_inc(x_26);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_append___redArg(x_25, x_16);
lean_dec_ref(x_16);
lean_inc(x_26);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_22);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_26);
x_41 = l_Lean_Syntax_node1(x_26, x_17, x_40);
x_42 = l_Lean_Syntax_node7(x_26, x_11, x_24, x_13, x_18, x_33, x_36, x_38, x_41);
x_43 = lean_box(x_12);
lean_inc(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(x_44, 0, x_42);
lean_closure_set(x_44, 1, x_2);
lean_closure_set(x_44, 2, x_43);
x_45 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(x_1, x_42, x_44, x_15, x_30, x_14, x_19, x_27, x_20, x_21);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Do_elabDoMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___redArg(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoMatch_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Do_doElemElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Match_0__Lean_Elab_Do_expandToTermMatch___closed__9));
x_4 = ((lean_object*)(l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___closed__2));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoMatch___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Match(uint8_t builtin);
lean_object* initialize_Lean_Elab_MatchAltView(uint8_t builtin);
lean_object* initialize_Lean_Data_Array(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Match(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MatchAltView(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Do_elabDoMatch___regBuiltin_Lean_Elab_Do_elabDoMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
