// Lean compiler output
// Module: Lean.Meta.Native
// Imports: public import Lean.Meta.Basic import Lean.Util.CollectLevelParams import Lean.Elab.DeclarationRange import Lean.Compiler.Options
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "` failed: Could not evaluate decidable instance. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` failed. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__10;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__0;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__1;
static const lean_array_object l_Lean_Meta_nativeEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_native"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 17, 188, 127, 248, 12, 59, 169)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__5 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__5_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 197, 108, 116, 168, 105, 88, 191)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__7_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ax"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__8 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 222, 122, 135, 172, 245, 68, 224)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__9 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__9_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__10 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__11 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__11_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__12;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__13;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__14;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__15;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__16 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__17 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__18;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` failed: Cannot native decide proposition with metavariables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__19 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__19_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__20;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` failed: Cannot native decide proposition with free variables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__21 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__21_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_prf_8_; lean_object* v___x_9_; 
v_prf_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_prf_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_prf_8_);
return v___x_9_;
}
else
{
return v_k_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object* v_t_22_, lean_object* v_success_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_22_, v_success_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_success_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_26_, v_success_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object* v_t_30_, lean_object* v_notTrue_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_30_, v_notTrue_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_notTrue_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_34_, v_notTrue_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = l_Lean_Elab_abortCommandExceptionId;
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___closed__0);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; lean_object* v_env_53_; lean_object* v___x_54_; lean_object* v_mctx_55_; lean_object* v_lctx_56_; lean_object* v_options_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_52_ = lean_st_ref_get(v___y_50_);
v_env_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_env_53_);
lean_dec(v___x_52_);
v___x_54_ = lean_st_ref_get(v___y_48_);
v_mctx_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_mctx_55_);
lean_dec(v___x_54_);
v_lctx_56_ = lean_ctor_get(v___y_47_, 2);
v_options_57_ = lean_ctor_get(v___y_49_, 2);
lean_inc_ref(v_options_57_);
lean_inc_ref(v_lctx_56_);
v___x_58_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_58_, 0, v_env_53_);
lean_ctor_set(v___x_58_, 1, v_mctx_55_);
lean_ctor_set(v___x_58_, 2, v_lctx_56_);
lean_ctor_set(v___x_58_, 3, v_options_57_);
v___x_59_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_msgData_46_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_ref_74_; lean_object* v___x_75_; lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_ref_74_ = lean_ctor_get(v___y_71_, 5);
v___x_75_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
lean_inc(v_ref_74_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_ref_74_);
lean_ctor_set(v___x_80_, 1, v_a_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(lean_object* v_x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v_x_92_, 1);
v___x_99_ = l_Lean_stringToMessageData(v_a_98_);
v___x_100_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_99_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v_x_92_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v_x_92_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v_x_92_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 0);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(lean_object* v_constName_116_, uint8_t v_checkMeta_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; lean_object* v_env_124_; uint8_t v___x_125_; 
v___x_123_ = lean_st_ref_get(v___y_121_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_ref(v_env_124_);
lean_dec(v___x_123_);
lean_inc(v_constName_116_);
v___x_125_ = lean_has_compile_error(v_env_124_, v_constName_116_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v_env_127_; lean_object* v_options_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = lean_st_ref_get(v___y_121_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v_options_128_ = lean_ctor_get(v___y_120_, 2);
v___x_129_ = l_Lean_Environment_evalConst___redArg(v_env_127_, v_options_128_, v_constName_116_, v_checkMeta_117_);
lean_dec(v_constName_116_);
lean_dec_ref(v_env_127_);
v___x_130_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_129_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; lean_object* v_env_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec_ref_known(v___x_131_, 1);
v___x_132_ = lean_st_ref_get(v___y_121_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_133_);
lean_dec(v___x_132_);
v_options_134_ = lean_ctor_get(v___y_120_, 2);
v___x_135_ = l_Lean_Environment_evalConst___redArg(v_env_133_, v_options_134_, v_constName_116_, v_checkMeta_117_);
lean_dec(v_constName_116_);
lean_dec_ref(v_env_133_);
v___x_136_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v___x_135_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
return v___x_136_;
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_constName_116_);
v_a_137_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_131_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_131_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg___boxed(lean_object* v_constName_145_, lean_object* v_checkMeta_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_checkMeta_boxed_152_; lean_object* v_res_153_; 
v_checkMeta_boxed_152_ = lean_unbox(v_checkMeta_146_);
v_res_153_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_145_, v_checkMeta_boxed_152_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object* v_auxDeclName_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_160_; lean_object* v___x_161_; 
v___x_160_ = 1;
v___x_161_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_auxDeclName_154_, v___x_160_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object* v_auxDeclName_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_auxDeclName_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(lean_object* v_00_u03b1_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___redArg();
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1___boxed(lean_object* v_00_u03b1_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__1(v_00_u03b1_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(lean_object* v_00_u03b1_183_, lean_object* v_constName_184_, uint8_t v_checkMeta_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___redArg(v_constName_184_, v_checkMeta_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_192_, lean_object* v_constName_193_, lean_object* v_checkMeta_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v_checkMeta_boxed_200_; lean_object* v_res_201_; 
v_checkMeta_boxed_200_ = lean_unbox(v_checkMeta_194_);
v_res_201_ = l_Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0(v_00_u03b1_192_, v_constName_193_, v_checkMeta_boxed_200_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___redArg(v_x_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0(v_00_u03b1_210_, v_x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_218_, lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_226_, v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object* v_e_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = l_Lean_Expr_hasMVar(v_e_234_);
v___x_238_ = lean_bool_not(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v_mctx_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; lean_object* v_cache_245_; lean_object* v_zetaDeltaFVarIds_246_; lean_object* v_postponed_247_; lean_object* v_diag_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v___x_239_ = lean_st_ref_get(v___y_235_);
v_mctx_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_mctx_240_);
lean_dec(v___x_239_);
v___x_241_ = l_Lean_instantiateMVarsCore(v_mctx_240_, v_e_234_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v___x_241_);
v___x_244_ = lean_st_ref_take(v___y_235_);
v_cache_245_ = lean_ctor_get(v___x_244_, 1);
v_zetaDeltaFVarIds_246_ = lean_ctor_get(v___x_244_, 2);
v_postponed_247_ = lean_ctor_get(v___x_244_, 3);
v_diag_248_ = lean_ctor_get(v___x_244_, 4);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_244_, 0);
lean_dec(v_unused_258_);
v___x_250_ = v___x_244_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_diag_248_);
lean_inc(v_postponed_247_);
lean_inc(v_zetaDeltaFVarIds_246_);
lean_inc(v_cache_245_);
lean_dec(v___x_244_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v_snd_243_);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_snd_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_cache_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_zetaDeltaFVarIds_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_postponed_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_diag_248_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_st_ref_set(v___y_235_, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_fst_242_);
return v___x_255_;
}
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_e_234_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object* v_e_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_260_, v___y_261_);
lean_dec(v___y_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object* v_e_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_264_, v___y_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object* v_e_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object* v_kind_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; lean_object* v_auxDeclNGen_282_; lean_object* v___x_283_; lean_object* v_env_284_; lean_object* v___x_285_; lean_object* v_fst_286_; lean_object* v_snd_287_; lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v_nextMacroScope_290_; lean_object* v_ngen_291_; lean_object* v_traceState_292_; lean_object* v_cache_293_; lean_object* v_messages_294_; lean_object* v_infoState_295_; lean_object* v_snapshotTasks_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
v___x_281_ = lean_st_ref_get(v___y_279_);
v_auxDeclNGen_282_ = lean_ctor_get(v___x_281_, 3);
lean_inc_ref(v_auxDeclNGen_282_);
lean_dec(v___x_281_);
v___x_283_ = lean_st_ref_get(v___y_279_);
v_env_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc_ref(v_env_284_);
lean_dec(v___x_283_);
v___x_285_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_284_, v_auxDeclNGen_282_, v_kind_278_);
v_fst_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_fst_286_);
v_snd_287_ = lean_ctor_get(v___x_285_, 1);
lean_inc(v_snd_287_);
lean_dec_ref(v___x_285_);
v___x_288_ = lean_st_ref_take(v___y_279_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
v_nextMacroScope_290_ = lean_ctor_get(v___x_288_, 1);
v_ngen_291_ = lean_ctor_get(v___x_288_, 2);
v_traceState_292_ = lean_ctor_get(v___x_288_, 4);
v_cache_293_ = lean_ctor_get(v___x_288_, 5);
v_messages_294_ = lean_ctor_get(v___x_288_, 6);
v_infoState_295_ = lean_ctor_get(v___x_288_, 7);
v_snapshotTasks_296_ = lean_ctor_get(v___x_288_, 8);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_288_, 3);
lean_dec(v_unused_306_);
v___x_298_ = v___x_288_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snapshotTasks_296_);
lean_inc(v_infoState_295_);
lean_inc(v_messages_294_);
lean_inc(v_cache_293_);
lean_inc(v_traceState_292_);
lean_inc(v_ngen_291_);
lean_inc(v_nextMacroScope_290_);
lean_inc(v_env_289_);
lean_dec(v___x_288_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 3, v_snd_287_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_env_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_nextMacroScope_290_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_ngen_291_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_snd_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_cache_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_messages_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_infoState_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_snapshotTasks_296_);
v___x_301_ = v_reuseFailAlloc_304_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_st_ref_set(v___y_279_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_fst_286_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_307_, v___y_308_);
lean_dec(v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_311_, v___y_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_324_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_opts_325_, lean_object* v_opt_326_){
_start:
{
lean_object* v_name_327_; lean_object* v_defValue_328_; lean_object* v_map_329_; lean_object* v___x_330_; 
v_name_327_ = lean_ctor_get(v_opt_326_, 0);
v_defValue_328_ = lean_ctor_get(v_opt_326_, 1);
v_map_329_ = lean_ctor_get(v_opts_325_, 0);
v___x_330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_329_, v_name_327_);
if (lean_obj_tag(v___x_330_) == 0)
{
uint8_t v___x_331_; 
v___x_331_ = lean_unbox(v_defValue_328_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_330_, 1);
if (lean_obj_tag(v_val_332_) == 1)
{
uint8_t v_v_333_; 
v_v_333_ = lean_ctor_get_uint8(v_val_332_, 0);
lean_dec_ref_known(v_val_332_, 0);
return v_v_333_;
}
else
{
uint8_t v___x_334_; 
lean_dec(v_val_332_);
v___x_334_ = lean_unbox(v_defValue_328_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_opts_335_, lean_object* v_opt_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v_opts_335_, v_opt_336_);
lean_dec_ref(v_opt_336_);
lean_dec_ref(v_opts_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_339_, lean_object* v_opt_340_){
_start:
{
lean_object* v_name_341_; lean_object* v_defValue_342_; lean_object* v_map_343_; lean_object* v___x_344_; 
v_name_341_ = lean_ctor_get(v_opt_340_, 0);
v_defValue_342_ = lean_ctor_get(v_opt_340_, 1);
v_map_343_ = lean_ctor_get(v_opts_339_, 0);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_343_, v_name_341_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_inc(v_defValue_342_);
return v_defValue_342_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_344_, 1);
if (lean_obj_tag(v_val_345_) == 3)
{
lean_object* v_v_346_; 
v_v_346_ = lean_ctor_get(v_val_345_, 0);
lean_inc(v_v_346_);
lean_dec_ref_known(v_val_345_, 1);
return v_v_346_;
}
else
{
lean_dec(v_val_345_);
lean_inc(v_defValue_342_);
return v_defValue_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_o_353_, lean_object* v_k_354_, uint8_t v_v_355_){
_start:
{
lean_object* v_map_356_; uint8_t v_hasTrace_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_371_; 
v_map_356_ = lean_ctor_get(v_o_353_, 0);
v_hasTrace_357_ = lean_ctor_get_uint8(v_o_353_, sizeof(void*)*1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_o_353_);
if (v_isSharedCheck_371_ == 0)
{
v___x_359_ = v_o_353_;
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_map_356_);
lean_dec(v_o_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_361_, 0, v_v_355_);
lean_inc(v_k_354_);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_354_, v___x_361_, v_map_356_);
if (v_hasTrace_357_ == 0)
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_366_; 
v___x_363_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___closed__1));
v___x_364_ = l_Lean_Name_isPrefixOf(v___x_363_, v_k_354_);
lean_dec(v_k_354_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_362_);
v___x_366_ = v___x_359_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_362_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_364_);
return v___x_366_;
}
}
else
{
lean_object* v___x_369_; 
lean_dec(v_k_354_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_362_);
v___x_369_ = v___x_359_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_362_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*1, v_hasTrace_357_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_o_372_, lean_object* v_k_373_, lean_object* v_v_374_){
_start:
{
uint8_t v_v_boxed_375_; lean_object* v_res_376_; 
v_v_boxed_375_ = lean_unbox(v_v_374_);
v_res_376_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_o_372_, v_k_373_, v_v_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_opts_377_, lean_object* v_opt_378_, uint8_t v_val_379_){
_start:
{
lean_object* v_name_380_; lean_object* v___x_381_; 
v_name_380_ = lean_ctor_get(v_opt_378_, 0);
lean_inc(v_name_380_);
lean_dec_ref(v_opt_378_);
v___x_381_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_opts_377_, v_name_380_, v_val_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_opts_382_, lean_object* v_opt_383_, lean_object* v_val_384_){
_start:
{
uint8_t v_val_boxed_385_; lean_object* v_res_386_; 
v_val_boxed_385_ = lean_unbox(v_val_384_);
v_res_386_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_opts_382_, v_opt_383_, v_val_boxed_385_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_389_ = l_Lean_stringToMessageData(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_401_ = l_Lean_mkConst(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_408_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
lean_ctor_set(v___x_408_, 3, v___x_407_);
lean_ctor_set(v___x_408_, 4, v___x_407_);
lean_ctor_set(v___x_408_, 5, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_tacticName_412_, lean_object* v_a_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___x_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_693_; 
v___x_431_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_409_, v___y_417_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_693_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_693_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_693_;
goto v_resetjp_433_;
}
v___jp_419_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_420_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_424_ = l_Lean_MessageData_ofName(v_tacticName_412_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Exception_toMessageData(v___y_421_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_429_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec_ref(v___y_416_);
return v___x_430_;
}
else
{
lean_dec_ref(v___y_421_);
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
return v___y_420_;
}
}
v_resetjp_433_:
{
lean_object* v___y_437_; lean_object* v___y_451_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_traceState_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_691_; 
v___x_462_ = lean_st_ref_take(v___y_417_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_462_, 1);
v_ngen_465_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_462_, 3);
v_traceState_467_ = lean_ctor_get(v___x_462_, 4);
v_messages_468_ = lean_ctor_get(v___x_462_, 6);
v_infoState_469_ = lean_ctor_get(v___x_462_, 7);
v_snapshotTasks_470_ = lean_ctor_get(v___x_462_, 8);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_462_, 5);
lean_dec(v_unused_692_);
v___x_472_ = v___x_462_;
v_isShared_473_ = v_isSharedCheck_691_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_traceState_467_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_462_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_691_;
goto v_resetjp_471_;
}
v___jp_436_:
{
if (lean_obj_tag(v___y_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___y_437_, 1);
v___x_438_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_a_432_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
v___x_440_ = l_Lean_Exception_isInterrupt(v_a_439_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
lean_inc(v_a_439_);
v___x_441_ = l_Lean_Exception_isRuntime(v_a_439_);
v___y_420_ = v___x_438_;
v___y_421_ = v_a_439_;
v___y_422_ = v___x_441_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___x_438_;
v___y_421_ = v_a_439_;
v___y_422_ = v___x_440_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_432_);
lean_dec_ref(v___y_416_);
lean_dec(v_tacticName_412_);
v_a_442_ = lean_ctor_get(v___y_437_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___y_437_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___y_437_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___y_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
v___jp_450_:
{
if (v___y_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec_ref(v___y_452_);
v___x_454_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_412_);
v___x_455_ = l_Lean_MessageData_ofName(v_tacticName_412_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_Exception_toMessageData(v___y_451_);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_460_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_437_ = v___x_461_;
goto v___jp_436_;
}
else
{
lean_dec_ref(v___y_451_);
v___y_437_ = v___y_452_;
goto v___jp_436_;
}
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_474_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_432_, 3);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v_a_432_);
lean_ctor_set(v___x_475_, 1, v___x_410_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v_a_432_);
lean_ctor_set(v___x_476_, 1, v___x_411_);
v___x_477_ = l_Lean_markMeta(v_env_463_, v_a_432_);
v___x_478_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 5, v___x_478_);
lean_ctor_set(v___x_472_, 0, v___x_477_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_traceState_467_);
lean_ctor_set(v_reuseFailAlloc_690_, 5, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_690_, 6, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_690_, 7, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_690_, 8, v_snapshotTasks_470_);
v___x_480_ = v_reuseFailAlloc_690_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_mctx_483_; lean_object* v_zetaDeltaFVarIds_484_; lean_object* v_postponed_485_; lean_object* v_diag_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_688_; 
v___x_481_ = lean_st_ref_set(v___y_417_, v___x_480_);
v___x_482_ = lean_st_ref_take(v___y_415_);
v_mctx_483_ = lean_ctor_get(v___x_482_, 0);
v_zetaDeltaFVarIds_484_ = lean_ctor_get(v___x_482_, 2);
v_postponed_485_ = lean_ctor_get(v___x_482_, 3);
v_diag_486_ = lean_ctor_get(v___x_482_, 4);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_482_, 1);
lean_dec(v_unused_689_);
v___x_488_ = v___x_482_;
v_isShared_489_ = v_isSharedCheck_688_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_diag_486_);
lean_inc(v_postponed_485_);
lean_inc(v_zetaDeltaFVarIds_484_);
lean_inc(v_mctx_483_);
lean_dec(v___x_482_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_688_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_mctx_483_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_zetaDeltaFVarIds_484_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_postponed_485_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_diag_486_);
v___x_492_ = v_reuseFailAlloc_687_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_options_495_; lean_object* v_env_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_493_ = lean_st_ref_set(v___y_415_, v___x_492_);
v___x_494_ = lean_st_ref_get(v___y_417_);
v_options_495_ = lean_ctor_get(v___y_416_, 2);
v_env_496_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(1);
v___x_498_ = 1;
v___x_499_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_499_, 0, v___x_475_);
lean_ctor_set(v___x_499_, 1, v_a_413_);
lean_ctor_set(v___x_499_, 2, v___x_497_);
lean_ctor_set(v___x_499_, 3, v___x_476_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*4, v___x_498_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v___x_499_);
v___x_501_ = v___x_434_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_686_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; uint8_t v___y_543_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; uint8_t v___y_608_; uint8_t v___x_629_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_664_; uint8_t v___x_685_; 
v___x_502_ = 1;
v___x_503_ = 0;
v___x_564_ = l_Lean_Elab_async;
lean_inc_ref(v_options_495_);
v___x_565_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v_options_495_, v___x_564_, v___x_503_);
v___x_566_ = l_Lean_diagnostics;
v___x_629_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_565_, v___x_566_);
v___x_685_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_496_);
lean_dec_ref(v_env_496_);
if (v___x_685_ == 0)
{
if (v___x_629_ == 0)
{
v___y_664_ = v___x_502_;
goto v___jp_663_;
}
else
{
v___y_664_ = v___x_685_;
goto v___jp_663_;
}
}
else
{
v___y_664_ = v___x_629_;
goto v___jp_663_;
}
v___jp_504_:
{
lean_object* v_fileName_510_; lean_object* v_fileMap_511_; lean_object* v_currRecDepth_512_; lean_object* v_ref_513_; lean_object* v_currNamespace_514_; lean_object* v_openDecls_515_; lean_object* v_initHeartbeats_516_; lean_object* v_maxHeartbeats_517_; lean_object* v_quotContext_518_; lean_object* v_currMacroScope_519_; lean_object* v_cancelTk_x3f_520_; uint8_t v_suppressElabErrors_521_; lean_object* v_inheritedTraceOptions_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_fileName_510_ = lean_ctor_get(v___y_508_, 0);
v_fileMap_511_ = lean_ctor_get(v___y_508_, 1);
v_currRecDepth_512_ = lean_ctor_get(v___y_508_, 3);
v_ref_513_ = lean_ctor_get(v___y_508_, 5);
v_currNamespace_514_ = lean_ctor_get(v___y_508_, 6);
v_openDecls_515_ = lean_ctor_get(v___y_508_, 7);
v_initHeartbeats_516_ = lean_ctor_get(v___y_508_, 8);
v_maxHeartbeats_517_ = lean_ctor_get(v___y_508_, 9);
v_quotContext_518_ = lean_ctor_get(v___y_508_, 10);
v_currMacroScope_519_ = lean_ctor_get(v___y_508_, 11);
v_cancelTk_x3f_520_ = lean_ctor_get(v___y_508_, 12);
v_suppressElabErrors_521_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_522_ = lean_ctor_get(v___y_508_, 13);
v_isSharedCheck_534_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v___y_508_, 4);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v___y_508_, 2);
lean_dec(v_unused_536_);
v___x_524_ = v___y_508_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_inheritedTraceOptions_522_);
lean_inc(v_cancelTk_x3f_520_);
lean_inc(v_currMacroScope_519_);
lean_inc(v_quotContext_518_);
lean_inc(v_maxHeartbeats_517_);
lean_inc(v_initHeartbeats_516_);
lean_inc(v_openDecls_515_);
lean_inc(v_currNamespace_514_);
lean_inc(v_ref_513_);
lean_inc(v_currRecDepth_512_);
lean_inc(v_fileMap_511_);
lean_inc(v_fileName_510_);
lean_dec(v___y_508_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_506_, v___y_505_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___x_526_);
lean_ctor_set(v___x_524_, 2, v___y_506_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fileName_510_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_fileMap_511_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___y_506_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_currRecDepth_512_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_533_, 5, v_ref_513_);
lean_ctor_set(v_reuseFailAlloc_533_, 6, v_currNamespace_514_);
lean_ctor_set(v_reuseFailAlloc_533_, 7, v_openDecls_515_);
lean_ctor_set(v_reuseFailAlloc_533_, 8, v_initHeartbeats_516_);
lean_ctor_set(v_reuseFailAlloc_533_, 9, v_maxHeartbeats_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 10, v_quotContext_518_);
lean_ctor_set(v_reuseFailAlloc_533_, 11, v_currMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_533_, 12, v_cancelTk_x3f_520_);
lean_ctor_set(v_reuseFailAlloc_533_, 13, v_inheritedTraceOptions_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*14 + 1, v_suppressElabErrors_521_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14, v___y_507_);
v___x_529_ = l_Lean_addAndCompile(v___x_501_, v___x_502_, v___x_503_, v___x_528_, v___y_509_);
lean_dec_ref(v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
v___y_437_ = v___x_529_;
goto v___jp_436_;
}
else
{
lean_object* v_a_530_; uint8_t v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_530_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc(v_a_530_);
v___x_532_ = l_Lean_Exception_isRuntime(v_a_530_);
v___y_451_ = v_a_530_;
v___y_452_ = v___x_529_;
v___y_453_ = v___x_532_;
goto v___jp_450_;
}
else
{
v___y_451_ = v_a_530_;
v___y_452_ = v___x_529_;
v___y_453_ = v___x_531_;
goto v___jp_450_;
}
}
}
}
}
v___jp_537_:
{
uint8_t v___x_544_; 
v___x_544_ = lean_bool_not(v___y_543_);
if (v___x_544_ == 0)
{
v___y_505_ = v___y_538_;
v___y_506_ = v___y_539_;
v___y_507_ = v___y_542_;
v___y_508_ = v___y_540_;
v___y_509_ = v___y_541_;
goto v___jp_504_;
}
else
{
lean_object* v___x_545_; lean_object* v_env_546_; lean_object* v_nextMacroScope_547_; lean_object* v_ngen_548_; lean_object* v_auxDeclNGen_549_; lean_object* v_traceState_550_; lean_object* v_messages_551_; lean_object* v_infoState_552_; lean_object* v_snapshotTasks_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v___x_545_ = lean_st_ref_take(v___y_541_);
v_env_546_ = lean_ctor_get(v___x_545_, 0);
v_nextMacroScope_547_ = lean_ctor_get(v___x_545_, 1);
v_ngen_548_ = lean_ctor_get(v___x_545_, 2);
v_auxDeclNGen_549_ = lean_ctor_get(v___x_545_, 3);
v_traceState_550_ = lean_ctor_get(v___x_545_, 4);
v_messages_551_ = lean_ctor_get(v___x_545_, 6);
v_infoState_552_ = lean_ctor_get(v___x_545_, 7);
v_snapshotTasks_553_ = lean_ctor_get(v___x_545_, 8);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_545_, 5);
lean_dec(v_unused_563_);
v___x_555_ = v___x_545_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snapshotTasks_553_);
lean_inc(v_infoState_552_);
lean_inc(v_messages_551_);
lean_inc(v_traceState_550_);
lean_inc(v_auxDeclNGen_549_);
lean_inc(v_ngen_548_);
lean_inc(v_nextMacroScope_547_);
lean_inc(v_env_546_);
lean_dec(v___x_545_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_Kernel_enableDiag(v_env_546_, v___y_542_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 5, v___x_478_);
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_547_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_548_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_traceState_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_messages_551_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_infoState_552_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_snapshotTasks_553_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_st_ref_set(v___y_541_, v___x_559_);
v___y_505_ = v___y_538_;
v___y_506_ = v___y_539_;
v___y_507_ = v___y_542_;
v___y_508_ = v___y_540_;
v___y_509_ = v___y_541_;
goto v___jp_504_;
}
}
}
}
v___jp_567_:
{
lean_object* v___x_573_; lean_object* v_fileName_574_; lean_object* v_fileMap_575_; lean_object* v_currRecDepth_576_; lean_object* v_ref_577_; lean_object* v_currNamespace_578_; lean_object* v_openDecls_579_; lean_object* v_initHeartbeats_580_; lean_object* v_maxHeartbeats_581_; lean_object* v_quotContext_582_; lean_object* v_currMacroScope_583_; lean_object* v_cancelTk_x3f_584_; uint8_t v_suppressElabErrors_585_; lean_object* v_inheritedTraceOptions_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_599_; 
v___x_573_ = lean_st_ref_get(v___y_572_);
v_fileName_574_ = lean_ctor_get(v___y_571_, 0);
v_fileMap_575_ = lean_ctor_get(v___y_571_, 1);
v_currRecDepth_576_ = lean_ctor_get(v___y_571_, 3);
v_ref_577_ = lean_ctor_get(v___y_571_, 5);
v_currNamespace_578_ = lean_ctor_get(v___y_571_, 6);
v_openDecls_579_ = lean_ctor_get(v___y_571_, 7);
v_initHeartbeats_580_ = lean_ctor_get(v___y_571_, 8);
v_maxHeartbeats_581_ = lean_ctor_get(v___y_571_, 9);
v_quotContext_582_ = lean_ctor_get(v___y_571_, 10);
v_currMacroScope_583_ = lean_ctor_get(v___y_571_, 11);
v_cancelTk_x3f_584_ = lean_ctor_get(v___y_571_, 12);
v_suppressElabErrors_585_ = lean_ctor_get_uint8(v___y_571_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_586_ = lean_ctor_get(v___y_571_, 13);
v_isSharedCheck_599_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; lean_object* v_unused_601_; 
v_unused_600_ = lean_ctor_get(v___y_571_, 4);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v___y_571_, 2);
lean_dec(v_unused_601_);
v___x_588_ = v___y_571_;
v_isShared_589_ = v_isSharedCheck_599_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_inheritedTraceOptions_586_);
lean_inc(v_cancelTk_x3f_584_);
lean_inc(v_currMacroScope_583_);
lean_inc(v_quotContext_582_);
lean_inc(v_maxHeartbeats_581_);
lean_inc(v_initHeartbeats_580_);
lean_inc(v_openDecls_579_);
lean_inc(v_currNamespace_578_);
lean_inc(v_ref_577_);
lean_inc(v_currRecDepth_576_);
lean_inc(v_fileMap_575_);
lean_inc(v_fileName_574_);
lean_dec(v___y_571_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_599_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_env_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_env_590_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_573_);
v___x_591_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_570_, v___y_569_);
lean_inc_ref(v___y_570_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 4, v___x_591_);
lean_ctor_set(v___x_588_, 2, v___y_570_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_fileName_574_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_fileMap_575_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___y_570_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_currRecDepth_576_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_ref_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_currNamespace_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_openDecls_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_initHeartbeats_580_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_maxHeartbeats_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 10, v_quotContext_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 11, v_currMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 12, v_cancelTk_x3f_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 13, v_inheritedTraceOptions_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_598_, sizeof(void*)*14 + 1, v_suppressElabErrors_585_);
v___x_593_ = v_reuseFailAlloc_598_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; uint8_t v___x_597_; 
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*14, v___y_568_);
v___x_594_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_595_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___y_570_, v___x_594_, v___x_502_);
v___x_596_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_595_, v___x_566_);
v___x_597_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_590_);
lean_dec_ref(v_env_590_);
if (v___x_597_ == 0)
{
if (v___x_596_ == 0)
{
v___y_538_ = v___y_569_;
v___y_539_ = v___x_595_;
v___y_540_ = v___x_593_;
v___y_541_ = v___y_572_;
v___y_542_ = v___x_596_;
v___y_543_ = v___x_502_;
goto v___jp_537_;
}
else
{
v___y_538_ = v___y_569_;
v___y_539_ = v___x_595_;
v___y_540_ = v___x_593_;
v___y_541_ = v___y_572_;
v___y_542_ = v___x_596_;
v___y_543_ = v___x_597_;
goto v___jp_537_;
}
}
else
{
v___y_538_ = v___y_569_;
v___y_539_ = v___x_595_;
v___y_540_ = v___x_593_;
v___y_541_ = v___y_572_;
v___y_542_ = v___x_596_;
v___y_543_ = v___x_596_;
goto v___jp_537_;
}
}
}
}
v___jp_602_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_bool_not(v___y_608_);
if (v___x_609_ == 0)
{
v___y_568_ = v___y_604_;
v___y_569_ = v___y_603_;
v___y_570_ = v___y_605_;
v___y_571_ = v___y_607_;
v___y_572_ = v___y_606_;
goto v___jp_567_;
}
else
{
lean_object* v___x_610_; lean_object* v_env_611_; lean_object* v_nextMacroScope_612_; lean_object* v_ngen_613_; lean_object* v_auxDeclNGen_614_; lean_object* v_traceState_615_; lean_object* v_messages_616_; lean_object* v_infoState_617_; lean_object* v_snapshotTasks_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v___x_610_ = lean_st_ref_take(v___y_606_);
v_env_611_ = lean_ctor_get(v___x_610_, 0);
v_nextMacroScope_612_ = lean_ctor_get(v___x_610_, 1);
v_ngen_613_ = lean_ctor_get(v___x_610_, 2);
v_auxDeclNGen_614_ = lean_ctor_get(v___x_610_, 3);
v_traceState_615_ = lean_ctor_get(v___x_610_, 4);
v_messages_616_ = lean_ctor_get(v___x_610_, 6);
v_infoState_617_ = lean_ctor_get(v___x_610_, 7);
v_snapshotTasks_618_ = lean_ctor_get(v___x_610_, 8);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_610_, 5);
lean_dec(v_unused_628_);
v___x_620_ = v___x_610_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snapshotTasks_618_);
lean_inc(v_infoState_617_);
lean_inc(v_messages_616_);
lean_inc(v_traceState_615_);
lean_inc(v_auxDeclNGen_614_);
lean_inc(v_ngen_613_);
lean_inc(v_nextMacroScope_612_);
lean_inc(v_env_611_);
lean_dec(v___x_610_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = l_Lean_Kernel_enableDiag(v_env_611_, v___y_604_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 5, v___x_478_);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_nextMacroScope_612_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_ngen_613_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_auxDeclNGen_614_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_traceState_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_messages_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_infoState_617_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_snapshotTasks_618_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_st_ref_set(v___y_606_, v___x_624_);
v___y_568_ = v___y_604_;
v___y_569_ = v___y_603_;
v___y_570_ = v___y_605_;
v___y_571_ = v___y_607_;
v___y_572_ = v___y_606_;
goto v___jp_567_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_633_; lean_object* v_fileName_634_; lean_object* v_fileMap_635_; lean_object* v_currRecDepth_636_; lean_object* v_ref_637_; lean_object* v_currNamespace_638_; lean_object* v_openDecls_639_; lean_object* v_initHeartbeats_640_; lean_object* v_maxHeartbeats_641_; lean_object* v_quotContext_642_; lean_object* v_currMacroScope_643_; lean_object* v_cancelTk_x3f_644_; uint8_t v_suppressElabErrors_645_; lean_object* v_inheritedTraceOptions_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_660_; 
v___x_633_ = lean_st_ref_get(v___y_632_);
v_fileName_634_ = lean_ctor_get(v___y_631_, 0);
v_fileMap_635_ = lean_ctor_get(v___y_631_, 1);
v_currRecDepth_636_ = lean_ctor_get(v___y_631_, 3);
v_ref_637_ = lean_ctor_get(v___y_631_, 5);
v_currNamespace_638_ = lean_ctor_get(v___y_631_, 6);
v_openDecls_639_ = lean_ctor_get(v___y_631_, 7);
v_initHeartbeats_640_ = lean_ctor_get(v___y_631_, 8);
v_maxHeartbeats_641_ = lean_ctor_get(v___y_631_, 9);
v_quotContext_642_ = lean_ctor_get(v___y_631_, 10);
v_currMacroScope_643_ = lean_ctor_get(v___y_631_, 11);
v_cancelTk_x3f_644_ = lean_ctor_get(v___y_631_, 12);
v_suppressElabErrors_645_ = lean_ctor_get_uint8(v___y_631_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_646_ = lean_ctor_get(v___y_631_, 13);
v_isSharedCheck_660_ = !lean_is_exclusive(v___y_631_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; lean_object* v_unused_662_; 
v_unused_661_ = lean_ctor_get(v___y_631_, 4);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v___y_631_, 2);
lean_dec(v_unused_662_);
v___x_648_ = v___y_631_;
v_isShared_649_ = v_isSharedCheck_660_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_inheritedTraceOptions_646_);
lean_inc(v_cancelTk_x3f_644_);
lean_inc(v_currMacroScope_643_);
lean_inc(v_quotContext_642_);
lean_inc(v_maxHeartbeats_641_);
lean_inc(v_initHeartbeats_640_);
lean_inc(v_openDecls_639_);
lean_inc(v_currNamespace_638_);
lean_inc(v_ref_637_);
lean_inc(v_currRecDepth_636_);
lean_inc(v_fileMap_635_);
lean_inc(v_fileName_634_);
lean_dec(v___y_631_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_660_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_env_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v_env_650_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_650_);
lean_dec(v___x_633_);
v___x_651_ = l_Lean_maxRecDepth;
v___x_652_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_565_, v___x_651_);
lean_inc_ref(v___x_565_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 4, v___x_652_);
lean_ctor_set(v___x_648_, 2, v___x_565_);
v___x_654_ = v___x_648_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_fileName_634_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_fileMap_635_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_currRecDepth_636_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_659_, 5, v_ref_637_);
lean_ctor_set(v_reuseFailAlloc_659_, 6, v_currNamespace_638_);
lean_ctor_set(v_reuseFailAlloc_659_, 7, v_openDecls_639_);
lean_ctor_set(v_reuseFailAlloc_659_, 8, v_initHeartbeats_640_);
lean_ctor_set(v_reuseFailAlloc_659_, 9, v_maxHeartbeats_641_);
lean_ctor_set(v_reuseFailAlloc_659_, 10, v_quotContext_642_);
lean_ctor_set(v_reuseFailAlloc_659_, 11, v_currMacroScope_643_);
lean_ctor_set(v_reuseFailAlloc_659_, 12, v_cancelTk_x3f_644_);
lean_ctor_set(v_reuseFailAlloc_659_, 13, v_inheritedTraceOptions_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*14 + 1, v_suppressElabErrors_645_);
v___x_654_ = v_reuseFailAlloc_659_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; uint8_t v___x_658_; 
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*14, v___x_629_);
v___x_655_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_656_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__2(v___x_565_, v___x_655_, v___x_503_);
v___x_657_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__3(v___x_656_, v___x_566_);
v___x_658_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_650_);
lean_dec_ref(v_env_650_);
if (v___x_658_ == 0)
{
if (v___x_657_ == 0)
{
v___y_603_ = v___x_651_;
v___y_604_ = v___x_657_;
v___y_605_ = v___x_656_;
v___y_606_ = v___y_632_;
v___y_607_ = v___x_654_;
v___y_608_ = v___x_502_;
goto v___jp_602_;
}
else
{
v___y_603_ = v___x_651_;
v___y_604_ = v___x_657_;
v___y_605_ = v___x_656_;
v___y_606_ = v___y_632_;
v___y_607_ = v___x_654_;
v___y_608_ = v___x_658_;
goto v___jp_602_;
}
}
else
{
v___y_603_ = v___x_651_;
v___y_604_ = v___x_657_;
v___y_605_ = v___x_656_;
v___y_606_ = v___y_632_;
v___y_607_ = v___x_654_;
v___y_608_ = v___x_657_;
goto v___jp_602_;
}
}
}
}
v___jp_663_:
{
uint8_t v___x_665_; 
v___x_665_ = lean_bool_not(v___y_664_);
if (v___x_665_ == 0)
{
lean_inc_ref(v___y_416_);
v___y_631_ = v___y_416_;
v___y_632_ = v___y_417_;
goto v___jp_630_;
}
else
{
lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v_nextMacroScope_668_; lean_object* v_ngen_669_; lean_object* v_auxDeclNGen_670_; lean_object* v_traceState_671_; lean_object* v_messages_672_; lean_object* v_infoState_673_; lean_object* v_snapshotTasks_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v___x_666_ = lean_st_ref_take(v___y_417_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_668_ = lean_ctor_get(v___x_666_, 1);
v_ngen_669_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_670_ = lean_ctor_get(v___x_666_, 3);
v_traceState_671_ = lean_ctor_get(v___x_666_, 4);
v_messages_672_ = lean_ctor_get(v___x_666_, 6);
v_infoState_673_ = lean_ctor_get(v___x_666_, 7);
v_snapshotTasks_674_ = lean_ctor_get(v___x_666_, 8);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_666_, 5);
lean_dec(v_unused_684_);
v___x_676_ = v___x_666_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snapshotTasks_674_);
lean_inc(v_infoState_673_);
lean_inc(v_messages_672_);
lean_inc(v_traceState_671_);
lean_inc(v_auxDeclNGen_670_);
lean_inc(v_ngen_669_);
lean_inc(v_nextMacroScope_668_);
lean_inc(v_env_667_);
lean_dec(v___x_666_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Kernel_enableDiag(v_env_667_, v___x_629_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 5, v___x_478_);
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_nextMacroScope_668_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_ngen_669_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_auxDeclNGen_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_traceState_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_messages_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_infoState_673_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_snapshotTasks_674_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_st_ref_set(v___y_417_, v___x_680_);
lean_inc_ref(v___y_416_);
v___y_631_ = v___y_416_;
v___y_632_ = v___y_417_;
goto v___jp_630_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_tacticName_697_, lean_object* v_a_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_694_, v___x_695_, v___x_696_, v_tacticName_697_, v_a_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(lean_object* v_stx_705_, lean_object* v___y_706_){
_start:
{
uint8_t v___x_708_; lean_object* v___x_709_; 
v___x_708_ = 0;
v___x_709_ = l_Lean_Syntax_getRange_x3f(v_stx_705_, v___x_708_);
if (lean_obj_tag(v___x_709_) == 1)
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_722_; 
v_val_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_722_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_722_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_722_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_fileMap_714_; lean_object* v_start_715_; lean_object* v_stop_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_fileMap_714_ = lean_ctor_get(v___y_706_, 1);
v_start_715_ = lean_ctor_get(v_val_710_, 0);
lean_inc(v_start_715_);
v_stop_716_ = lean_ctor_get(v_val_710_, 1);
lean_inc(v_stop_716_);
lean_dec(v_val_710_);
lean_inc_ref(v_fileMap_714_);
v___x_717_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_714_, v_start_715_, v_stop_716_);
lean_dec(v_stop_716_);
lean_dec(v_start_715_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v___x_709_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg___boxed(lean_object* v_stx_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_725_, v___y_726_);
lean_dec_ref(v___y_726_);
lean_dec(v_stx_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(lean_object* v_declName_729_, lean_object* v_declRanges_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_Name_isAnonymous(v_declName_729_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v_env_736_; lean_object* v_nextMacroScope_737_; lean_object* v_ngen_738_; lean_object* v_auxDeclNGen_739_; lean_object* v_traceState_740_; lean_object* v_messages_741_; lean_object* v_infoState_742_; lean_object* v_snapshotTasks_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_771_; 
v___x_735_ = lean_st_ref_take(v___y_732_);
v_env_736_ = lean_ctor_get(v___x_735_, 0);
v_nextMacroScope_737_ = lean_ctor_get(v___x_735_, 1);
v_ngen_738_ = lean_ctor_get(v___x_735_, 2);
v_auxDeclNGen_739_ = lean_ctor_get(v___x_735_, 3);
v_traceState_740_ = lean_ctor_get(v___x_735_, 4);
v_messages_741_ = lean_ctor_get(v___x_735_, 6);
v_infoState_742_ = lean_ctor_get(v___x_735_, 7);
v_snapshotTasks_743_ = lean_ctor_get(v___x_735_, 8);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_735_, 5);
lean_dec(v_unused_772_);
v___x_745_ = v___x_735_;
v_isShared_746_ = v_isSharedCheck_771_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snapshotTasks_743_);
lean_inc(v_infoState_742_);
lean_inc(v_messages_741_);
lean_inc(v_traceState_740_);
lean_inc(v_auxDeclNGen_739_);
lean_inc(v_ngen_738_);
lean_inc(v_nextMacroScope_737_);
lean_inc(v_env_736_);
lean_dec(v___x_735_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_771_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_747_ = l_Lean_declRangeExt;
v___x_748_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_747_, v_env_736_, v_declName_729_, v_declRanges_730_);
v___x_749_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 5, v___x_749_);
lean_ctor_set(v___x_745_, 0, v___x_748_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_nextMacroScope_737_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_ngen_738_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_auxDeclNGen_739_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_traceState_740_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_770_, 6, v_messages_741_);
lean_ctor_set(v_reuseFailAlloc_770_, 7, v_infoState_742_);
lean_ctor_set(v_reuseFailAlloc_770_, 8, v_snapshotTasks_743_);
v___x_751_ = v_reuseFailAlloc_770_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_mctx_754_; lean_object* v_zetaDeltaFVarIds_755_; lean_object* v_postponed_756_; lean_object* v_diag_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_768_; 
v___x_752_ = lean_st_ref_set(v___y_732_, v___x_751_);
v___x_753_ = lean_st_ref_take(v___y_731_);
v_mctx_754_ = lean_ctor_get(v___x_753_, 0);
v_zetaDeltaFVarIds_755_ = lean_ctor_get(v___x_753_, 2);
v_postponed_756_ = lean_ctor_get(v___x_753_, 3);
v_diag_757_ = lean_ctor_get(v___x_753_, 4);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_753_, 1);
lean_dec(v_unused_769_);
v___x_759_ = v___x_753_;
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_diag_757_);
lean_inc(v_postponed_756_);
lean_inc(v_zetaDeltaFVarIds_755_);
lean_inc(v_mctx_754_);
lean_dec(v___x_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_768_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_mctx_754_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_zetaDeltaFVarIds_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_postponed_756_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_diag_757_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_st_ref_set(v___y_731_, v___x_763_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v_declRanges_730_);
lean_dec(v_declName_729_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg___boxed(lean_object* v_declName_775_, lean_object* v_declRanges_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_775_, v_declRanges_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec(v___y_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_declName_781_, lean_object* v_rangeStx_782_, lean_object* v_selectionRangeStx_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v___x_789_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_rangeStx_782_, v___y_786_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
if (lean_obj_tag(v_a_790_) == 1)
{
lean_object* v_val_794_; lean_object* v___x_795_; lean_object* v_a_796_; lean_object* v_a_798_; 
lean_del_object(v___x_792_);
v_val_794_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v_a_790_, 1);
v___x_795_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_selectionRangeStx_783_, v___y_786_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
if (lean_obj_tag(v_a_796_) == 0)
{
lean_inc(v_val_794_);
v_a_798_ = v_val_794_;
goto v___jp_797_;
}
else
{
lean_object* v_val_801_; 
v_val_801_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_796_, 1);
v_a_798_ = v_val_801_;
goto v___jp_797_;
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_val_794_);
lean_ctor_set(v___x_799_, 1, v_a_798_);
v___x_800_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_781_, v___x_799_, v___y_785_, v___y_787_);
return v___x_800_;
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_a_790_);
lean_dec(v_declName_781_);
v___x_802_ = lean_box(0);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_802_);
v___x_804_ = v___x_792_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_declName_807_, lean_object* v_rangeStx_808_, lean_object* v_selectionRangeStx_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_declName_807_, v_rangeStx_808_, v_selectionRangeStx_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v_selectionRangeStx_809_);
lean_dec(v_rangeStx_808_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
if (lean_obj_tag(v_a_816_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = l_List_reverse___redArg(v_a_817_);
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_829_; 
v_head_819_ = lean_ctor_get(v_a_816_, 0);
v_tail_820_ = lean_ctor_get(v_a_816_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_829_ == 0)
{
v___x_822_ = v_a_816_;
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tail_820_);
lean_inc(v_head_819_);
lean_dec(v_a_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Lean_mkLevelParam(v_head_819_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_a_817_);
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_817_);
v___x_826_ = v_reuseFailAlloc_828_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v_a_816_ = v_tail_820_;
v_a_817_ = v___x_826_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(lean_object* v_env_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v_nextMacroScope_835_; lean_object* v_ngen_836_; lean_object* v_auxDeclNGen_837_; lean_object* v_traceState_838_; lean_object* v_messages_839_; lean_object* v_infoState_840_; lean_object* v_snapshotTasks_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
v___x_834_ = lean_st_ref_take(v___y_832_);
v_nextMacroScope_835_ = lean_ctor_get(v___x_834_, 1);
v_ngen_836_ = lean_ctor_get(v___x_834_, 2);
v_auxDeclNGen_837_ = lean_ctor_get(v___x_834_, 3);
v_traceState_838_ = lean_ctor_get(v___x_834_, 4);
v_messages_839_ = lean_ctor_get(v___x_834_, 6);
v_infoState_840_ = lean_ctor_get(v___x_834_, 7);
v_snapshotTasks_841_ = lean_ctor_get(v___x_834_, 8);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v___x_834_, 5);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_869_);
v___x_843_ = v___x_834_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snapshotTasks_841_);
lean_inc(v_infoState_840_);
lean_inc(v_messages_839_);
lean_inc(v_traceState_838_);
lean_inc(v_auxDeclNGen_837_);
lean_inc(v_ngen_836_);
lean_inc(v_nextMacroScope_835_);
lean_dec(v___x_834_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 5, v___x_845_);
lean_ctor_set(v___x_843_, 0, v_env_830_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_env_830_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_nextMacroScope_835_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_ngen_836_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_auxDeclNGen_837_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_traceState_838_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_866_, 6, v_messages_839_);
lean_ctor_set(v_reuseFailAlloc_866_, 7, v_infoState_840_);
lean_ctor_set(v_reuseFailAlloc_866_, 8, v_snapshotTasks_841_);
v___x_847_ = v_reuseFailAlloc_866_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_mctx_850_; lean_object* v_zetaDeltaFVarIds_851_; lean_object* v_postponed_852_; lean_object* v_diag_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
v___x_848_ = lean_st_ref_set(v___y_832_, v___x_847_);
v___x_849_ = lean_st_ref_take(v___y_831_);
v_mctx_850_ = lean_ctor_get(v___x_849_, 0);
v_zetaDeltaFVarIds_851_ = lean_ctor_get(v___x_849_, 2);
v_postponed_852_ = lean_ctor_get(v___x_849_, 3);
v_diag_853_ = lean_ctor_get(v___x_849_, 4);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v___x_849_, 1);
lean_dec(v_unused_865_);
v___x_855_ = v___x_849_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_diag_853_);
lean_inc(v_postponed_852_);
lean_inc(v_zetaDeltaFVarIds_851_);
lean_inc(v_mctx_850_);
lean_dec(v___x_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_mctx_850_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_zetaDeltaFVarIds_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_postponed_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_diag_853_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_st_ref_set(v___y_831_, v___x_859_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg___boxed(lean_object* v_env_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(lean_object* v_env_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v_env_883_; lean_object* v_a_885_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_882_ = lean_st_ref_get(v___y_880_);
v_env_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc_ref(v_env_883_);
lean_dec(v___x_882_);
v___x_895_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_875_, v___y_878_, v___y_880_);
lean_dec_ref(v___x_895_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
v___x_896_ = lean_apply_5(v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_883_, v___y_878_, v___y_880_);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_906_);
v___x_900_ = v___x_898_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_898_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v_a_897_);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_897_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_896_, 1);
v_a_885_ = v_a_907_;
goto v___jp_884_;
}
v___jp_884_:
{
lean_object* v___x_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v___x_886_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_883_, v___y_878_, v___y_880_);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_894_);
v___x_888_ = v___x_886_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_dec(v___x_886_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 0, v_a_885_);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_885_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg___boxed(lean_object* v_env_908_, lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_908_, v_x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
v___x_917_ = lean_unsigned_to_nat(16u);
v___x_918_ = lean_mk_array(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_925_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
lean_ctor_set(v___x_926_, 2, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = l_Lean_Level_ofNat(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_945_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_946_ = l_Lean_mkConst(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_box(0);
v___x_948_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_949_ = l_Lean_mkConst(v___x_948_, v___x_947_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
v___x_955_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_956_ = l_Lean_mkConst(v___x_955_, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_963_, lean_object* v_e_964_, lean_object* v_axiomDeclRange_x3f_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___x_1086_; 
v___x_979_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_964_, v_a_967_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_1086_ = l_Lean_Expr_hasFVar(v_a_980_);
if (v___x_1086_ == 0)
{
v___y_1065_ = v_a_966_;
v___y_1066_ = v_a_967_;
v___y_1067_ = v_a_968_;
v___y_1068_ = v_a_969_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1088_ = l_Lean_MessageData_ofName(v_tacticName_963_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_indentExpr(v_a_980_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1093_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
v___jp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = lean_box(0);
v___x_975_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_973_, v___x_974_);
v___x_976_ = l_Lean_mkConst(v___y_972_, v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
v___jp_981_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_params_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1061_; 
v___x_986_ = lean_st_ref_get(v___y_985_);
v___x_987_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_980_);
v___x_988_ = l_Lean_collectLevelParams(v___x_987_, v_a_980_);
v_params_989_ = lean_ctor_get(v___x_988_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; 
v_unused_1062_ = lean_ctor_get(v___x_988_, 1);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v___x_988_, 0);
lean_dec(v_unused_1063_);
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1061_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_params_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1061_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_env_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_env_993_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_993_);
lean_dec(v___x_986_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_array_to_list(v_params_989_);
v___x_996_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_963_);
v___x_997_ = l_Lean_Name_append(v___x_996_, v_tacticName_963_);
v___x_998_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_997_);
v___x_999_ = l_Lean_Name_append(v___x_997_, v___x_998_);
lean_inc(v_a_980_);
lean_inc(v___x_995_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1000_, 0, v___x_999_);
lean_closure_set(v___f_1000_, 1, v___x_995_);
lean_closure_set(v___f_1000_, 2, v___x_994_);
lean_closure_set(v___f_1000_, 3, v_tacticName_963_);
lean_closure_set(v___f_1000_, 4, v_a_980_);
v___x_1001_ = l_Lean_Environment_unlockAsync(v_env_993_);
v___x_1002_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v___x_1001_, v___f_1000_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1052_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1052_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1052_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_unbox(v_a_1003_);
lean_dec(v_a_1003_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec(v___x_997_);
lean_dec(v___x_995_);
lean_del_object(v___x_991_);
lean_dec(v_a_980_);
v___x_1008_ = lean_box(1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1051_; 
lean_del_object(v___x_1005_);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1013_ = l_Lean_Name_append(v___x_997_, v___x_1012_);
v___x_1014_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1013_, v___y_985_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1051_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1051_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1019_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1020_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1022_ = l_Lean_mkApp3(v___x_1019_, v___x_1020_, v_a_980_, v___x_1021_);
lean_inc(v___x_995_);
lean_inc(v_a_1015_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 2, v___x_1022_);
lean_ctor_set(v___x_991_, 1, v___x_995_);
lean_ctor_set(v___x_991_, 0, v_a_1015_);
v___x_1024_ = v___x_991_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1015_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1025_ = 0;
v___x_1026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_1025_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1026_);
v___x_1028_ = v___x_1017_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_addDecl(v___x_1028_, v___x_1025_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref_known(v___x_1029_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_965_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_val_1030_ = lean_ctor_get(v_axiomDeclRange_x3f_965_, 0);
v___x_1031_ = lean_box(0);
lean_inc(v_a_1015_);
v___x_1032_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7(v_a_1015_, v_val_1030_, v___x_1031_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_dec_ref_known(v___x_1032_, 1);
v___y_972_ = v_a_1015_;
v___y_973_ = v___x_995_;
goto v___jp_971_;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_1015_);
lean_dec(v___x_995_);
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
v___y_972_ = v_a_1015_;
v___y_973_ = v___x_995_;
goto v___jp_971_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1015_);
lean_dec(v___x_995_);
v_a_1041_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1029_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1029_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___x_997_);
lean_dec(v___x_995_);
lean_del_object(v___x_991_);
lean_dec(v_a_980_);
v_a_1053_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1002_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1002_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
v___jp_1064_:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Expr_hasMVar(v_a_980_);
if (v___x_1069_ == 0)
{
v___y_982_ = v___y_1065_;
v___y_983_ = v___y_1066_;
v___y_984_ = v___y_1067_;
v___y_985_ = v___y_1068_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v___x_1070_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1071_ = l_Lean_MessageData_ofName(v_tacticName_963_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_indentExpr(v_a_980_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1076_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1103_, lean_object* v_e_1104_, lean_object* v_axiomDeclRange_x3f_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1103_, v_e_1104_, v_axiomDeclRange_x3f_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_axiomDeclRange_x3f_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(lean_object* v_env_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___redArg(v_env_1112_, v___y_1114_, v___y_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6___boxed(lean_object* v_env_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5_spec__6(v_env_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_00_u03b1_1126_, lean_object* v_env_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___redArg(v_env_1127_, v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_env_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__5(v_00_u03b1_1135_, v_env_1136_, v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(lean_object* v_stx_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___redArg(v_stx_1144_, v___y_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9___boxed(lean_object* v_stx_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__9(v_stx_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v_stx_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(lean_object* v_declName_1158_, lean_object* v_declRanges_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___redArg(v_declName_1158_, v_declRanges_1159_, v___y_1161_, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10___boxed(lean_object* v_declName_1166_, lean_object* v_declRanges_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__7_spec__10(v_declName_1166_, v_declRanges_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Native(builtin);
}
#ifdef __cplusplus
}
#endif
