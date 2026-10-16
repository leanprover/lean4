// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: public import Lean.Elab.PreDefinition.WF.PackMutual public import Lean.Elab.PreDefinition.WF.FloatRecApp public import Lean.Elab.PreDefinition.WF.Rel public import Lean.Elab.PreDefinition.WF.Fix public import Lean.Elab.PreDefinition.WF.Unfold public import Lean.Elab.PreDefinition.WF.Preprocess public import Lean.Elab.PreDefinition.WF.GuessLex
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "well-founded recursion cannot be used, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not take any (non-fixed) arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "marking functions defined by well-founded recursion as `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is not effective"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfRel: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wfRecursion: expected unary function type: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_wfRecursion___closed__2 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">> "};
static const lean_object* l_Lean_Elab_wfRecursion___closed__3 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__3_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__4;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " :=\n"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__5 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__5_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__6;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unaryPreDefProcessed:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__7 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__7_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__8;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unaryPreDef:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__9 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__9_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__10;
static const lean_ctor_object l_Lean_Elab_wfRecursion___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_wfRecursion___boxed__const__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 60, 146, 67, 170, 35, 9, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 191, 24, 173, 99, 110, 250, 159)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(183, 176, 152, 199, 88, 244, 126, 231)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 192, 220, 42, 201, 36, 231, 139)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 8, 70, 241, 95, 177, 39, 230)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 164, 65, 123, 204, 166, 116, 237)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 212, 71, 249, 113, 26, 236, 1)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 192, 221, 228, 155, 175, 93, 246)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 119, 48, 4, 113, 111, 251, 171)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 104, 40, 162, 247, 89, 56, 248)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 159, 143, 175, 93, 190, 135, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 178, 65, 214, 219, 44, 29, 26)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1197449596) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 70, 68, 25, 255, 132, 81, 38)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 173, 23, 241, 152, 14, 79, 23)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 207, 166, 163, 30, 74, 122, 49)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 76, 225, 120, 116, 96, 87, 123)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_6_);
lean_ctor_set(v___x_7_, 5, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object* v_env_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v_nextMacroScope_13_; lean_object* v_ngen_14_; lean_object* v_auxDeclNGen_15_; lean_object* v_traceState_16_; lean_object* v_recordedDeps_17_; lean_object* v_messages_18_; lean_object* v_infoState_19_; lean_object* v_snapshotTasks_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_46_; 
v___x_12_ = lean_st_ref_take(v___y_10_);
v_nextMacroScope_13_ = lean_ctor_get(v___x_12_, 1);
v_ngen_14_ = lean_ctor_get(v___x_12_, 2);
v_auxDeclNGen_15_ = lean_ctor_get(v___x_12_, 3);
v_traceState_16_ = lean_ctor_get(v___x_12_, 4);
v_recordedDeps_17_ = lean_ctor_get(v___x_12_, 6);
v_messages_18_ = lean_ctor_get(v___x_12_, 7);
v_infoState_19_ = lean_ctor_get(v___x_12_, 8);
v_snapshotTasks_20_ = lean_ctor_get(v___x_12_, 9);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; lean_object* v_unused_48_; 
v_unused_47_ = lean_ctor_get(v___x_12_, 5);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_48_);
v___x_22_ = v___x_12_;
v_isShared_23_ = v_isSharedCheck_46_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snapshotTasks_20_);
lean_inc(v_infoState_19_);
lean_inc(v_messages_18_);
lean_inc(v_recordedDeps_17_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_15_);
lean_inc(v_ngen_14_);
lean_inc(v_nextMacroScope_13_);
lean_dec(v___x_12_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_46_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 5, v___x_24_);
lean_ctor_set(v___x_22_, 0, v_env_8_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_8_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_13_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v_ngen_14_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_15_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v_traceState_16_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_recordedDeps_17_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_messages_18_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_infoState_19_);
lean_ctor_set(v_reuseFailAlloc_45_, 9, v_snapshotTasks_20_);
v___x_26_ = v_reuseFailAlloc_45_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_mctx_29_; lean_object* v_zetaDeltaFVarIds_30_; lean_object* v_postponed_31_; lean_object* v_diag_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_43_; 
v___x_27_ = lean_st_ref_put(v___y_10_, v___x_26_);
v___x_28_ = lean_st_ref_take(v___y_9_);
v_mctx_29_ = lean_ctor_get(v___x_28_, 0);
v_zetaDeltaFVarIds_30_ = lean_ctor_get(v___x_28_, 2);
v_postponed_31_ = lean_ctor_get(v___x_28_, 3);
v_diag_32_ = lean_ctor_get(v___x_28_, 4);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_28_, 1);
lean_dec(v_unused_44_);
v___x_34_ = v___x_28_;
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_diag_32_);
lean_inc(v_postponed_31_);
lean_inc(v_zetaDeltaFVarIds_30_);
lean_inc(v_mctx_29_);
lean_dec(v___x_28_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_37_);
v___x_39_ = v___x_34_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_mctx_29_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v_zetaDeltaFVarIds_30_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v_postponed_31_);
lean_ctor_set(v_reuseFailAlloc_42_, 4, v_diag_32_);
v___x_39_ = v_reuseFailAlloc_42_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_st_ref_put(v___y_9_, v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_36_);
return v___x_41_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec(v___y_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_54_, v___y_58_, v___y_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v_b_75_, lean_object* v_c_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; 
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
v___x_82_ = lean_apply_9(v_k_72_, v_b_75_, v_c_76_, v___y_73_, v___y_74_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v_b_86_, lean_object* v_c_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_83_, v___y_84_, v___y_85_, v_b_86_, v_c_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_94_, lean_object* v_maxFVars_x3f_95_, lean_object* v_k_96_, uint8_t v_cleanupAnnotations_97_, uint8_t v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_106_, 0, v_k_96_);
lean_closure_set(v___f_106_, 1, v___y_99_);
lean_closure_set(v___f_106_, 2, v___y_100_);
v___x_107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_94_, v_maxFVars_x3f_95_, v___f_106_, v_cleanupAnnotations_97_, v_whnfType_98_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_107_) == 0)
{
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_116_, lean_object* v_maxFVars_x3f_117_, lean_object* v_k_118_, lean_object* v_cleanupAnnotations_119_, lean_object* v_whnfType_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_128_; uint8_t v_whnfType_boxed_129_; lean_object* v_res_130_; 
v_cleanupAnnotations_boxed_128_ = lean_unbox(v_cleanupAnnotations_119_);
v_whnfType_boxed_129_ = lean_unbox(v_whnfType_120_);
v_res_130_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_116_, v_maxFVars_x3f_117_, v_k_118_, v_cleanupAnnotations_boxed_128_, v_whnfType_boxed_129_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_131_, lean_object* v_type_132_, lean_object* v_maxFVars_x3f_133_, lean_object* v_k_134_, uint8_t v_cleanupAnnotations_135_, uint8_t v_whnfType_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_132_, v_maxFVars_x3f_133_, v_k_134_, v_cleanupAnnotations_135_, v_whnfType_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_145_, lean_object* v_type_146_, lean_object* v_maxFVars_x3f_147_, lean_object* v_k_148_, lean_object* v_cleanupAnnotations_149_, lean_object* v_whnfType_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_158_; uint8_t v_whnfType_boxed_159_; lean_object* v_res_160_; 
v_cleanupAnnotations_boxed_158_ = lean_unbox(v_cleanupAnnotations_149_);
v_whnfType_boxed_159_ = lean_unbox(v_whnfType_150_);
v_res_160_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_145_, v_type_146_, v_maxFVars_x3f_147_, v_k_148_, v_cleanupAnnotations_boxed_158_, v_whnfType_boxed_159_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_as_161_, size_t v_sz_162_, size_t v_i_163_, lean_object* v_b_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = lean_usize_dec_lt(v_i_163_, v_sz_162_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_b_164_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v_a_171_ = lean_array_uget_borrowed(v_as_161_, v_i_163_);
v___x_172_ = l_Lean_Elab_addAsAxiom___redArg(v_a_171_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_172_) == 0)
{
size_t v___x_173_; size_t v___x_174_; 
lean_dec_ref_known(v___x_172_, 1);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_add(v_i_163_, v___x_173_);
v_i_163_ = v___x_174_;
v_b_164_ = v___x_170_;
goto _start;
}
else
{
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_as_176_, lean_object* v_sz_177_, lean_object* v_i_178_, lean_object* v_b_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
size_t v_sz_boxed_183_; size_t v_i_boxed_184_; lean_object* v_res_185_; 
v_sz_boxed_183_ = lean_unbox_usize(v_sz_177_);
lean_dec(v_sz_177_);
v_i_boxed_184_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_176_, v_sz_boxed_183_, v_i_boxed_184_, v_b_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec_ref(v_as_176_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object* v_a_186_, size_t v_sz_187_, size_t v_i_188_, lean_object* v_bs_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_lt(v_i_188_, v_sz_187_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_dec_ref(v_a_186_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_bs_189_);
return v___x_196_;
}
else
{
lean_object* v_v_197_; lean_object* v___x_198_; lean_object* v_bs_x27_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_v_197_ = lean_array_uget(v_bs_189_, v_i_188_);
v___x_198_ = lean_unsigned_to_nat(0u);
v_bs_x27_199_ = lean_array_uset(v_bs_189_, v_i_188_, v___x_198_);
v___x_200_ = lean_usize_to_nat(v_i_188_);
lean_inc_ref(v_a_186_);
v___x_201_ = l_Lean_Elab_WF_varyingVarNames(v_a_186_, v___x_200_, v_v_197_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_add(v_i_188_, v___x_203_);
v___x_205_ = lean_array_uset(v_bs_x27_199_, v_i_188_, v_a_202_);
v_i_188_ = v___x_204_;
v_bs_189_ = v___x_205_;
goto _start;
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref(v_bs_x27_199_);
lean_dec_ref(v_a_186_);
v_a_207_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_201_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_201_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object* v_a_215_, lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
size_t v_sz_boxed_224_; size_t v_i_boxed_225_; lean_object* v_res_226_; 
v_sz_boxed_224_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_225_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_215_, v_sz_boxed_224_, v_i_boxed_225_, v_bs_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_226_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(1);
v___x_228_ = l_Lean_MessageData_ofFormat(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_233_ = l_Lean_MessageData_ofFormat(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
return v_x_234_;
}
else
{
lean_object* v_head_236_; lean_object* v_tail_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_259_; 
v_head_236_ = lean_ctor_get(v_x_235_, 0);
v_tail_237_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_259_ == 0)
{
v___x_239_ = v_x_235_;
v_isShared_240_ = v_isSharedCheck_259_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_tail_237_);
lean_inc(v_head_236_);
lean_dec(v_x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_259_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_before_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_257_; 
v_before_241_ = lean_ctor_get(v_head_236_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v_head_236_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_head_236_, 1);
lean_dec(v_unused_258_);
v___x_243_ = v_head_236_;
v_isShared_244_ = v_isSharedCheck_257_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_before_241_);
lean_dec(v_head_236_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_257_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 7);
lean_ctor_set(v___x_243_, 1, v___x_245_);
lean_ctor_set(v___x_243_, 0, v_x_234_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_x_234_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_256_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 7);
lean_ctor_set(v___x_239_, 1, v___x_248_);
lean_ctor_set(v___x_239_, 0, v___x_247_);
v___x_250_ = v___x_239_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_255_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_MessageData_ofSyntax(v_before_241_);
v___x_252_ = l_Lean_indentD(v___x_251_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_250_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v_x_234_ = v___x_253_;
v_x_235_ = v_tail_237_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_260_, lean_object* v_opt_261_){
_start:
{
lean_object* v_name_262_; lean_object* v_defValue_263_; lean_object* v_map_264_; lean_object* v___x_265_; 
v_name_262_ = lean_ctor_get(v_opt_261_, 0);
v_defValue_263_ = lean_ctor_get(v_opt_261_, 1);
v_map_264_ = lean_ctor_get(v_opts_260_, 0);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_264_, v_name_262_);
if (lean_obj_tag(v___x_265_) == 0)
{
uint8_t v___x_266_; 
v___x_266_ = lean_unbox(v_defValue_263_);
return v___x_266_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v___x_265_, 1);
if (lean_obj_tag(v_val_267_) == 1)
{
uint8_t v_v_268_; 
v_v_268_ = lean_ctor_get_uint8(v_val_267_, 0);
lean_dec_ref_known(v_val_267_, 0);
return v_v_268_;
}
else
{
uint8_t v___x_269_; 
lean_dec(v_val_267_);
v___x_269_ = lean_unbox(v_defValue_263_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_270_, lean_object* v_opt_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_270_, v_opt_271_);
lean_dec_ref(v_opt_271_);
lean_dec_ref(v_opts_270_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_278_ = l_Lean_MessageData_ofFormat(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_279_, lean_object* v_macroStack_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_281_);
v___x_284_ = l_Lean_Elab_pp_macroStack;
v___x_285_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v___x_283_, v___x_284_);
lean_dec_ref(v___x_283_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v_macroStack_280_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_msgData_279_);
return v___x_286_;
}
else
{
if (lean_obj_tag(v_macroStack_280_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_msgData_279_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_after_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_304_; 
v_head_288_ = lean_ctor_get(v_macroStack_280_, 0);
lean_inc(v_head_288_);
v_after_289_ = lean_ctor_get(v_head_288_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_head_288_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_head_288_, 0);
lean_dec(v_unused_305_);
v___x_291_ = v_head_288_;
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_after_289_);
lean_dec(v_head_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_293_);
lean_ctor_set(v___x_291_, 0, v_msgData_279_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_msgData_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_303_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_msgData_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_MessageData_ofSyntax(v_after_289_);
v___x_299_ = l_Lean_indentD(v___x_298_);
v_msgData_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_300_, 0, v___x_297_);
lean_ctor_set(v_msgData_300_, 1, v___x_299_);
v___x_301_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_300_, v_macroStack_280_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_306_, lean_object* v_macroStack_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_306_, v_macroStack_307_, v___y_308_);
lean_dec_ref(v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_env_318_; uint8_t v___x_319_; lean_object* v_env_320_; lean_object* v___x_321_; lean_object* v_toCold_322_; lean_object* v_mctx_323_; lean_object* v_lctx_324_; lean_object* v_options_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = 0;
v_env_320_ = l_Lean_Environment_setRecordingDeps(v_env_318_, v___x_319_);
v___x_321_ = lean_st_ref_get(v___y_313_);
v_toCold_322_ = lean_ctor_get(v___y_314_, 0);
v_mctx_323_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_mctx_323_);
lean_dec(v___x_321_);
v_lctx_324_ = lean_ctor_get(v___y_312_, 2);
v_options_325_ = lean_ctor_get(v_toCold_322_, 2);
lean_inc_ref(v_options_325_);
lean_inc_ref(v_lctx_324_);
v___x_326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_326_, 0, v_env_320_);
lean_ctor_set(v___x_326_, 1, v_mctx_323_);
lean_ctor_set(v___x_326_, 2, v_lctx_324_);
lean_ctor_set(v___x_326_, 3, v_options_325_);
v___x_327_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_msgData_311_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_ref_344_; lean_object* v_macroStack_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_ref_344_ = lean_ctor_get(v___y_341_, 2);
v_macroStack_345_ = lean_ctor_get(v___y_337_, 1);
v___x_346_ = l_Lean_Elab_getBetterRef(v_ref_344_, v_macroStack_345_);
v___x_347_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_336_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v___x_347_);
lean_inc(v_macroStack_345_);
v___x_349_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_348_, v_macroStack_345_, v___y_341_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_346_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object* v_as_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_a_386_; uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_b_377_);
return v___x_391_;
}
else
{
lean_object* v_array_392_; lean_object* v_start_393_; lean_object* v_stop_394_; uint8_t v___x_395_; 
v_array_392_ = lean_ctor_get(v_b_377_, 0);
v_start_393_ = lean_ctor_get(v_b_377_, 1);
v_stop_394_ = lean_ctor_get(v_b_377_, 2);
v___x_395_ = lean_nat_dec_lt(v_start_393_, v_stop_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_b_377_);
return v___x_396_;
}
else
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_425_; 
lean_inc(v_stop_394_);
lean_inc(v_start_393_);
lean_inc_ref(v_array_392_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_b_377_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_426_ = lean_ctor_get(v_b_377_, 2);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_b_377_, 1);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_b_377_, 0);
lean_dec(v_unused_428_);
v___x_398_ = v_b_377_;
v_isShared_399_ = v_isSharedCheck_425_;
goto v_resetjp_397_;
}
else
{
lean_dec(v_b_377_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_425_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v_a_400_ = lean_array_uget_borrowed(v_as_374_, v_i_376_);
v___x_401_ = lean_array_fget(v_array_392_, v_start_393_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_start_393_, v___x_402_);
lean_dec(v_start_393_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_403_);
v___x_405_ = v___x_398_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_array_392_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_stop_394_);
v___x_405_ = v_reuseFailAlloc_424_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_array_get_size(v_a_400_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v___x_401_);
v_a_386_ = v___x_405_;
goto v___jp_385_;
}
else
{
lean_object* v_declName_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_declName_409_ = lean_ctor_get(v___x_401_, 3);
lean_inc(v_declName_409_);
lean_dec(v___x_401_);
v___x_410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1);
v___x_411_ = l_Lean_MessageData_ofName(v_declName_409_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_414_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_dec_ref_known(v___x_415_, 1);
v_a_386_ = v___x_405_;
goto v___jp_385_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v___x_405_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
}
}
v___jp_385_:
{
size_t v___x_387_; size_t v___x_388_; 
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_376_, v___x_387_);
v_i_376_ = v___x_388_;
v_b_377_ = v_a_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_as_429_, lean_object* v_sz_430_, lean_object* v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
size_t v_sz_boxed_440_; size_t v_i_boxed_441_; lean_object* v_res_442_; 
v_sz_boxed_440_ = lean_unbox_usize(v_sz_430_);
lean_dec(v_sz_430_);
v_i_boxed_441_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_429_, v_sz_boxed_440_, v_i_boxed_441_, v_b_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_as_429_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t v_sz_443_, size_t v_i_444_, lean_object* v_bs_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_lt(v_i_444_, v_sz_443_);
if (v___x_446_ == 0)
{
return v_bs_445_;
}
else
{
lean_object* v_v_447_; lean_object* v_declName_448_; lean_object* v___x_449_; lean_object* v_bs_x27_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
v_v_447_ = lean_array_uget_borrowed(v_bs_445_, v_i_444_);
v_declName_448_ = lean_ctor_get(v_v_447_, 3);
lean_inc(v_declName_448_);
v___x_449_ = lean_unsigned_to_nat(0u);
v_bs_x27_450_ = lean_array_uset(v_bs_445_, v_i_444_, v___x_449_);
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_444_, v___x_451_);
v___x_453_ = lean_array_uset(v_bs_x27_450_, v_i_444_, v_declName_448_);
v_i_444_ = v___x_452_;
v_bs_445_ = v___x_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_bs_457_){
_start:
{
size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_sz_boxed_458_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_459_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_boxed_458_, v_i_boxed_459_, v_bs_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_a_461_, lean_object* v___x_462_, size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v___x_462_);
lean_dec_ref(v_a_461_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_bs_465_);
return v___x_470_;
}
else
{
lean_object* v_v_471_; lean_object* v_ref_472_; uint8_t v_kind_473_; lean_object* v_levelParams_474_; lean_object* v_modifiers_475_; lean_object* v_declName_476_; lean_object* v_binders_477_; lean_object* v_numSectionVars_478_; lean_object* v_type_479_; lean_object* v_value_480_; lean_object* v_termination_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_507_; 
v_v_471_ = lean_array_uget(v_bs_465_, v_i_464_);
v_ref_472_ = lean_ctor_get(v_v_471_, 0);
v_kind_473_ = lean_ctor_get_uint8(v_v_471_, sizeof(void*)*9);
v_levelParams_474_ = lean_ctor_get(v_v_471_, 1);
v_modifiers_475_ = lean_ctor_get(v_v_471_, 2);
v_declName_476_ = lean_ctor_get(v_v_471_, 3);
v_binders_477_ = lean_ctor_get(v_v_471_, 4);
v_numSectionVars_478_ = lean_ctor_get(v_v_471_, 5);
v_type_479_ = lean_ctor_get(v_v_471_, 6);
v_value_480_ = lean_ctor_get(v_v_471_, 7);
v_termination_481_ = lean_ctor_get(v_v_471_, 8);
v_isSharedCheck_507_ = !lean_is_exclusive(v_v_471_);
if (v_isSharedCheck_507_ == 0)
{
v___x_483_ = v_v_471_;
v_isShared_484_ = v_isSharedCheck_507_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_termination_481_);
lean_inc(v_value_480_);
lean_inc(v_type_479_);
lean_inc(v_numSectionVars_478_);
lean_inc(v_binders_477_);
lean_inc(v_declName_476_);
lean_inc(v_modifiers_475_);
lean_inc(v_levelParams_474_);
lean_inc(v_ref_472_);
lean_dec(v_v_471_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_507_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
size_t v_sz_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; size_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_sz_485_ = lean_array_size(v_a_461_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_486_);
v___x_488_ = ((size_t)0ULL);
lean_inc_ref(v_a_461_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_485_, v___x_488_, v_a_461_);
lean_inc(v___x_462_);
v___x_490_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_489_, v___x_462_, v_value_480_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 7, v_a_491_);
v___x_493_ = v___x_483_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_ref_472_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_levelParams_474_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_modifiers_475_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_declName_476_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_binders_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_numSectionVars_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_type_479_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_a_491_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_termination_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_498_, sizeof(void*)*9, v_kind_473_);
v___x_493_ = v_reuseFailAlloc_498_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_464_, v___x_494_);
v___x_496_ = lean_array_uset(v_bs_x27_487_, v_i_464_, v___x_493_);
v_i_464_ = v___x_495_;
v_bs_465_ = v___x_496_;
goto _start;
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_bs_x27_487_);
lean_del_object(v___x_483_);
lean_dec_ref(v_termination_481_);
lean_dec_ref(v_type_479_);
lean_dec(v_numSectionVars_478_);
lean_dec(v_binders_477_);
lean_dec(v_declName_476_);
lean_dec_ref(v_modifiers_475_);
lean_dec(v_levelParams_474_);
lean_dec(v_ref_472_);
lean_dec(v___x_462_);
lean_dec_ref(v_a_461_);
v_a_499_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_a_508_, lean_object* v___x_509_, lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_bs_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_517_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_508_, v___x_509_, v_sz_boxed_516_, v_i_boxed_517_, v_bs_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_519_, size_t v_sz_520_, size_t v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_519_, v_sz_520_, v___x_521_, v___x_522_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v___x_532_; 
lean_dec_ref_known(v___x_531_, 1);
lean_inc_ref(v_a_519_);
v___x_532_ = l_Lean_Elab_getFixedParamPerms(v_a_519_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_n(v_a_533_, 2);
lean_dec_ref_known(v___x_532_, 1);
lean_inc_ref(v_a_519_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_533_, v_sz_520_, v___x_521_, v_a_519_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; size_t v_sz_539_; lean_object* v___x_540_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_array_get_size(v_a_519_);
lean_inc_ref(v_a_519_);
v___x_538_ = l_Array_toSubarray___redArg(v_a_519_, v___x_536_, v___x_537_);
v_sz_539_ = lean_array_size(v_a_535_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_a_535_, v_sz_539_, v___x_521_, v___x_538_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_541_; lean_object* v_numSectionVars_542_; lean_object* v___x_543_; 
lean_dec_ref_known(v___x_540_, 1);
v___x_541_ = lean_array_get_borrowed(v___x_523_, v_a_519_, v___x_536_);
v_numSectionVars_542_ = lean_ctor_get(v___x_541_, 5);
lean_inc(v_numSectionVars_542_);
lean_inc_ref(v_a_519_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_519_, v_numSectionVars_542_, v_sz_520_, v___x_521_, v_a_519_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
lean_inc(v_a_535_);
lean_inc(v_a_533_);
v___x_545_ = l_Lean_Elab_WF_packMutual(v_a_533_, v_a_535_, v_a_544_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_535_);
lean_ctor_set(v___x_550_, 1, v_a_546_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_a_533_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_535_);
lean_dec(v_a_533_);
v_a_556_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_545_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_a_535_);
lean_dec(v_a_533_);
v_a_564_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_543_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_a_535_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_519_);
v_a_572_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_540_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_540_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_a_533_);
lean_dec_ref(v_a_519_);
v_a_580_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_534_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_534_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_a_519_);
v_a_588_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_532_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_532_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_a_519_);
v_a_596_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_531_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_531_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_604_, lean_object* v_sz_605_, lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v___x_44045__boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_605_);
lean_dec(v_sz_605_);
v___x_44045__boxed_617_ = lean_unbox_usize(v___x_606_);
lean_dec(v___x_606_);
v_res_618_ = l_Lean_Elab_wfRecursion___lam__0(v_a_604_, v_sz_boxed_616_, v___x_44045__boxed_617_, v___x_607_, v___x_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v___x_608_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_619_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_ref_628_; uint8_t v_kind_629_; lean_object* v_levelParams_630_; lean_object* v_modifiers_631_; lean_object* v_declName_632_; lean_object* v_binders_633_; lean_object* v_numSectionVars_634_; lean_object* v_type_635_; lean_object* v_value_636_; lean_object* v_termination_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref_known(v___x_627_, 1);
v_ref_628_ = lean_ctor_get(v_snd_619_, 0);
v_kind_629_ = lean_ctor_get_uint8(v_snd_619_, sizeof(void*)*9);
v_levelParams_630_ = lean_ctor_get(v_snd_619_, 1);
v_modifiers_631_ = lean_ctor_get(v_snd_619_, 2);
v_declName_632_ = lean_ctor_get(v_snd_619_, 3);
v_binders_633_ = lean_ctor_get(v_snd_619_, 4);
v_numSectionVars_634_ = lean_ctor_get(v_snd_619_, 5);
v_type_635_ = lean_ctor_get(v_snd_619_, 6);
v_value_636_ = lean_ctor_get(v_snd_619_, 7);
v_termination_637_ = lean_ctor_get(v_snd_619_, 8);
v_isSharedCheck_663_ = !lean_is_exclusive(v_snd_619_);
if (v_isSharedCheck_663_ == 0)
{
v___x_639_ = v_snd_619_;
v_isShared_640_ = v_isSharedCheck_663_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_termination_637_);
lean_inc(v_value_636_);
lean_inc(v_type_635_);
lean_inc(v_numSectionVars_634_);
lean_inc(v_binders_633_);
lean_inc(v_declName_632_);
lean_inc(v_modifiers_631_);
lean_inc(v_levelParams_630_);
lean_inc(v_ref_628_);
lean_dec(v_snd_619_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_663_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Elab_WF_preprocess(v_value_636_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_654_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_expr_646_; lean_object* v___x_648_; 
v_expr_646_ = lean_ctor_get(v_a_642_, 0);
lean_inc_ref(v_expr_646_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 7, v_expr_646_);
v___x_648_ = v___x_639_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_ref_628_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_levelParams_630_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_modifiers_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_declName_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_binders_633_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v_numSectionVars_634_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_type_635_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_expr_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v_termination_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_653_, sizeof(void*)*9, v_kind_629_);
v___x_648_ = v_reuseFailAlloc_653_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_649_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_639_);
lean_dec_ref(v_termination_637_);
lean_dec_ref(v_type_635_);
lean_dec(v_numSectionVars_634_);
lean_dec(v_binders_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_modifiers_631_);
lean_dec(v_levelParams_630_);
lean_dec(v_ref_628_);
v_a_655_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_641_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_641_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref(v_snd_619_);
v_a_664_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_627_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_627_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_toCold_692_; lean_object* v_options_693_; uint8_t v_hasTrace_694_; 
v_toCold_692_ = lean_ctor_get(v___y_689_, 0);
v_options_693_ = lean_ctor_get(v_toCold_692_, 2);
v_hasTrace_694_ = lean_ctor_get_uint8(v_options_693_, sizeof(void*)*1);
if (v_hasTrace_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v___x_684_);
v___x_695_ = lean_box(v_hasTrace_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_inheritedTraceOptions_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_inheritedTraceOptions_697_ = lean_ctor_get(v_toCold_692_, 11);
v___x_698_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
v___x_699_ = l_Lean_Name_append(v___x_698_, v___x_684_);
v___x_700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_697_, v_options_693_, v___x_699_);
lean_dec(v___x_699_);
v___x_701_ = lean_box(v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v___x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_wfRecursion___lam__2(v___x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 1)
{
lean_object* v_pre_721_; 
v_pre_721_ = lean_ctor_get(v_x_720_, 0);
switch(lean_obj_tag(v_pre_721_))
{
case 1:
{
lean_object* v_pre_722_; 
v_pre_722_ = lean_ctor_get(v_pre_721_, 0);
switch(lean_obj_tag(v_pre_722_))
{
case 0:
{
lean_object* v_str_723_; lean_object* v_str_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_str_723_ = lean_ctor_get(v_x_720_, 1);
v_str_724_ = lean_ctor_get(v_pre_721_, 1);
v___x_725_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_726_ = lean_string_dec_eq(v_str_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_728_ = lean_string_dec_eq(v_str_724_, v___x_727_);
if (v___x_728_ == 0)
{
return v___x_728_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_730_ = lean_string_dec_eq(v_str_723_, v___x_729_);
if (v___x_730_ == 0)
{
return v___x_730_;
}
else
{
return v_suppressElabErrors_719_;
}
}
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_732_ = lean_string_dec_eq(v_str_723_, v___x_731_);
if (v___x_732_ == 0)
{
return v___x_732_;
}
else
{
return v_suppressElabErrors_719_;
}
}
}
case 1:
{
lean_object* v_pre_733_; 
v_pre_733_ = lean_ctor_get(v_pre_722_, 0);
if (lean_obj_tag(v_pre_733_) == 0)
{
lean_object* v_str_734_; lean_object* v_str_735_; lean_object* v_str_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_str_734_ = lean_ctor_get(v_x_720_, 1);
v_str_735_ = lean_ctor_get(v_pre_721_, 1);
v_str_736_ = lean_ctor_get(v_pre_722_, 1);
v___x_737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_738_ = lean_string_dec_eq(v_str_736_, v___x_737_);
if (v___x_738_ == 0)
{
return v___x_738_;
}
else
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_740_ = lean_string_dec_eq(v_str_735_, v___x_739_);
if (v___x_740_ == 0)
{
return v___x_740_;
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_742_ = lean_string_dec_eq(v_str_734_, v___x_741_);
if (v___x_742_ == 0)
{
return v___x_742_;
}
else
{
return v_suppressElabErrors_719_;
}
}
}
}
else
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
}
default: 
{
uint8_t v___x_744_; 
v___x_744_ = 0;
return v___x_744_;
}
}
}
case 0:
{
lean_object* v_str_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_str_745_ = lean_ctor_get(v_x_720_, 1);
v___x_746_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_747_ = lean_string_dec_eq(v_str_745_, v___x_746_);
if (v___x_747_ == 0)
{
return v___x_747_;
}
else
{
return v_suppressElabErrors_719_;
}
}
default: 
{
uint8_t v___x_748_; 
v___x_748_ = 0;
return v___x_748_;
}
}
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_suppressElabErrors_boxed_752_; uint8_t v_res_753_; lean_object* v_r_754_; 
v_suppressElabErrors_boxed_752_ = lean_unbox(v_suppressElabErrors_750_);
v_res_753_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_752_, v_x_751_);
lean_dec(v_x_751_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_756_, lean_object* v_msgData_757_, uint8_t v_severity_758_, uint8_t v_isSilent_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v_toCold_773_; lean_object* v___y_774_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; lean_object* v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; uint8_t v___y_835_; lean_object* v___y_836_; uint8_t v___y_840_; uint8_t v___y_841_; uint8_t v___x_851_; uint8_t v___y_853_; uint8_t v___x_859_; 
v___x_851_ = 2;
v___x_859_ = l_Lean_instBEqMessageSeverity_beq(v_severity_758_, v___x_851_);
if (v___x_859_ == 0)
{
v___y_853_ = v___x_859_;
goto v___jp_852_;
}
else
{
uint8_t v___x_860_; 
lean_inc_ref(v_msgData_757_);
v___x_860_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_757_);
if (v___x_860_ == 0)
{
v___y_853_ = v___x_860_;
goto v___jp_852_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v_msgData_757_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
v___jp_765_:
{
lean_object* v_currNamespace_775_; lean_object* v_openDecls_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v_nextMacroScope_782_; lean_object* v_ngen_783_; lean_object* v_auxDeclNGen_784_; lean_object* v_traceState_785_; lean_object* v_cache_786_; lean_object* v_recordedDeps_787_; lean_object* v_messages_788_; lean_object* v_infoState_789_; lean_object* v_snapshotTasks_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_801_; 
v_currNamespace_775_ = lean_ctor_get(v_toCold_773_, 4);
v_openDecls_776_ = lean_ctor_get(v_toCold_773_, 5);
lean_inc(v_openDecls_776_);
lean_inc(v_currNamespace_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_currNamespace_775_);
lean_ctor_set(v___x_777_, 1, v_openDecls_776_);
v___x_778_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___y_771_);
lean_inc_ref(v___y_769_);
lean_inc_ref(v___y_772_);
v___x_779_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_779_, 0, v___y_772_);
lean_ctor_set(v___x_779_, 1, v___y_766_);
lean_ctor_set(v___x_779_, 2, v___y_767_);
lean_ctor_set(v___x_779_, 3, v___y_769_);
lean_ctor_set(v___x_779_, 4, v___x_778_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*5, v___y_768_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*5 + 1, v___y_770_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*5 + 2, v_isSilent_759_);
v___x_780_ = lean_st_ref_take(v___y_774_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
v_nextMacroScope_782_ = lean_ctor_get(v___x_780_, 1);
v_ngen_783_ = lean_ctor_get(v___x_780_, 2);
v_auxDeclNGen_784_ = lean_ctor_get(v___x_780_, 3);
v_traceState_785_ = lean_ctor_get(v___x_780_, 4);
v_cache_786_ = lean_ctor_get(v___x_780_, 5);
v_recordedDeps_787_ = lean_ctor_get(v___x_780_, 6);
v_messages_788_ = lean_ctor_get(v___x_780_, 7);
v_infoState_789_ = lean_ctor_get(v___x_780_, 8);
v_snapshotTasks_790_ = lean_ctor_get(v___x_780_, 9);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_801_ == 0)
{
v___x_792_ = v___x_780_;
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snapshotTasks_790_);
lean_inc(v_infoState_789_);
lean_inc(v_messages_788_);
lean_inc(v_recordedDeps_787_);
lean_inc(v_cache_786_);
lean_inc(v_traceState_785_);
lean_inc(v_auxDeclNGen_784_);
lean_inc(v_ngen_783_);
lean_inc(v_nextMacroScope_782_);
lean_inc(v_env_781_);
lean_dec(v___x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_801_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = lean_box(0);
v___x_795_ = l_Lean_MessageLog_add(v___x_779_, v_messages_788_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 7, v___x_795_);
v___x_797_ = v___x_792_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_env_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_nextMacroScope_782_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_ngen_783_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_auxDeclNGen_784_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_traceState_785_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v_cache_786_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_recordedDeps_787_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_infoState_789_);
lean_ctor_set(v_reuseFailAlloc_800_, 9, v_snapshotTasks_790_);
v___x_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_st_ref_put(v___y_774_, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_794_);
return v___x_799_;
}
}
}
v___jp_802_:
{
lean_object* v_fileName_811_; lean_object* v_fileMap_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_828_; 
v_fileName_811_ = lean_ctor_get(v___y_805_, 0);
v_fileMap_812_ = lean_ctor_get(v___y_805_, 1);
v___x_813_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_757_);
v___x_814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_813_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_828_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_inc_ref_n(v_fileMap_812_, 2);
v___x_819_ = l_Lean_FileMap_toPosition(v_fileMap_812_, v___y_807_);
lean_dec(v___y_807_);
v___x_820_ = l_Lean_FileMap_toPosition(v_fileMap_812_, v___y_810_);
lean_dec(v___y_810_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_806_ == 0)
{
lean_del_object(v___x_817_);
lean_dec_ref(v___y_804_);
v___y_766_ = v___x_819_;
v___y_767_ = v___x_821_;
v___y_768_ = v___y_808_;
v___y_769_ = v___x_822_;
v___y_770_ = v___y_809_;
v___y_771_ = v_a_815_;
v___y_772_ = v_fileName_811_;
v_toCold_773_ = v___y_803_;
v___y_774_ = v___y_763_;
goto v___jp_765_;
}
else
{
uint8_t v___x_823_; 
lean_inc(v_a_815_);
v___x_823_ = l_Lean_MessageData_hasTag(v___y_804_, v_a_815_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_dec_ref_known(v___x_821_, 1);
lean_dec_ref(v___x_819_);
lean_dec(v_a_815_);
v___x_824_ = lean_box(0);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_del_object(v___x_817_);
v___y_766_ = v___x_819_;
v___y_767_ = v___x_821_;
v___y_768_ = v___y_808_;
v___y_769_ = v___x_822_;
v___y_770_ = v___y_809_;
v___y_771_ = v_a_815_;
v___y_772_ = v_fileName_811_;
v_toCold_773_ = v___y_803_;
v___y_774_ = v___y_763_;
goto v___jp_765_;
}
}
}
}
v___jp_829_:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Syntax_getTailPos_x3f(v___y_833_, v___y_834_);
lean_dec(v___y_833_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_inc(v___y_836_);
v___y_803_ = v___y_830_;
v___y_804_ = v___y_832_;
v___y_805_ = v___y_830_;
v___y_806_ = v___y_831_;
v___y_807_ = v___y_836_;
v___y_808_ = v___y_834_;
v___y_809_ = v___y_835_;
v___y_810_ = v___y_836_;
goto v___jp_802_;
}
else
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_837_, 1);
v___y_803_ = v___y_830_;
v___y_804_ = v___y_832_;
v___y_805_ = v___y_830_;
v___y_806_ = v___y_831_;
v___y_807_ = v___y_836_;
v___y_808_ = v___y_834_;
v___y_809_ = v___y_835_;
v___y_810_ = v_val_838_;
goto v___jp_802_;
}
}
v___jp_839_:
{
lean_object* v_toCold_842_; lean_object* v_ref_843_; uint8_t v_suppressElabErrors_844_; lean_object* v___x_845_; lean_object* v___f_846_; lean_object* v_ref_847_; lean_object* v___x_848_; 
v_toCold_842_ = lean_ctor_get(v___y_762_, 0);
v_ref_843_ = lean_ctor_get(v___y_762_, 2);
v_suppressElabErrors_844_ = lean_ctor_get_uint8(v___y_762_, sizeof(void*)*3 + 2);
v___x_845_ = lean_box(v_suppressElabErrors_844_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_846_, 0, v___x_845_);
v_ref_847_ = l_Lean_replaceRef(v_ref_756_, v_ref_843_);
v___x_848_ = l_Lean_Syntax_getPos_x3f(v_ref_847_, v___y_840_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___y_830_ = v_toCold_842_;
v___y_831_ = v_suppressElabErrors_844_;
v___y_832_ = v___f_846_;
v___y_833_ = v_ref_847_;
v___y_834_ = v___y_840_;
v___y_835_ = v___y_841_;
v___y_836_ = v___x_849_;
goto v___jp_829_;
}
else
{
lean_object* v_val_850_; 
v_val_850_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___x_848_, 1);
v___y_830_ = v_toCold_842_;
v___y_831_ = v_suppressElabErrors_844_;
v___y_832_ = v___f_846_;
v___y_833_ = v_ref_847_;
v___y_834_ = v___y_840_;
v___y_835_ = v___y_841_;
v___y_836_ = v_val_850_;
goto v___jp_829_;
}
}
v___jp_852_:
{
uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = 1;
v___x_855_ = l_Lean_instBEqMessageSeverity_beq(v_severity_758_, v___x_854_);
if (v___x_855_ == 0)
{
v___y_840_ = v___y_853_;
v___y_841_ = v_severity_758_;
goto v___jp_839_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_856_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_762_);
v___x_857_ = l_Lean_warningAsError;
v___x_858_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v___x_856_, v___x_857_);
lean_dec_ref(v___x_856_);
if (v___x_858_ == 0)
{
v___y_840_ = v___y_853_;
v___y_841_ = v_severity_758_;
goto v___jp_839_;
}
else
{
v___y_840_ = v___y_853_;
v___y_841_ = v___x_851_;
goto v___jp_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_863_, lean_object* v_msgData_864_, lean_object* v_severity_865_, lean_object* v_isSilent_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_severity_boxed_872_; uint8_t v_isSilent_boxed_873_; lean_object* v_res_874_; 
v_severity_boxed_872_ = lean_unbox(v_severity_865_);
v_isSilent_boxed_873_ = lean_unbox(v_isSilent_866_);
v_res_874_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_863_, v_msgData_864_, v_severity_boxed_872_, v_isSilent_boxed_873_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_ref_863_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_875_, lean_object* v_msgData_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = 1;
v___x_885_ = 0;
v___x_886_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_875_, v_msgData_876_, v___x_884_, v___x_885_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_887_, lean_object* v_msgData_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_887_, v_msgData_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v_ref_887_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_905_, lean_object* v_as_906_, size_t v_i_907_, size_t v_stop_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_a_918_; uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_eq(v_i_907_, v_stop_908_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v_name_924_; lean_object* v_stx_925_; uint8_t v___y_927_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_923_ = lean_array_uget_borrowed(v_as_906_, v_i_907_);
v_name_924_ = lean_ctor_get(v___x_923_, 0);
v_stx_925_ = lean_ctor_get(v___x_923_, 1);
v___x_937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_938_ = lean_name_eq(v_name_924_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_940_ = lean_name_eq(v_name_924_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
v_a_918_ = v___x_941_;
goto v___jp_917_;
}
else
{
v___y_927_ = v___x_940_;
goto v___jp_926_;
}
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_nat_dec_lt(v___x_942_, v___x_905_);
v___y_927_ = v___x_943_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_924_);
v___x_929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_924_, v___y_927_);
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
v___x_934_ = l_Lean_MessageData_ofFormat(v___x_933_);
v___x_935_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_925_, v___x_934_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v_a_918_ = v_a_936_;
goto v___jp_917_;
}
else
{
return v___x_935_;
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_909_);
return v___x_944_;
}
v___jp_917_:
{
size_t v___x_919_; size_t v___x_920_; 
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_907_, v___x_919_);
v_i_907_ = v___x_920_;
v_b_909_ = v_a_918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_945_, lean_object* v_as_946_, lean_object* v_i_947_, lean_object* v_stop_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_i_boxed_957_; size_t v_stop_boxed_958_; lean_object* v_res_959_; 
v_i_boxed_957_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_stop_boxed_958_ = lean_unbox_usize(v_stop_948_);
lean_dec(v_stop_948_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_945_, v_as_946_, v_i_boxed_957_, v_stop_boxed_958_, v_b_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_as_946_);
lean_dec(v___x_945_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_960_, lean_object* v_as_961_, size_t v_i_962_, size_t v_stop_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_a_973_; uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_eq(v_i_962_, v_stop_963_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v_modifiers_979_; lean_object* v_attrs_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_978_ = lean_array_uget_borrowed(v_as_961_, v_i_962_);
v_modifiers_979_ = lean_ctor_get(v___x_978_, 2);
v_attrs_980_ = lean_ctor_get(v_modifiers_979_, 2);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_attrs_980_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_984_ == 0)
{
v_a_973_ = v___x_983_;
goto v___jp_972_;
}
else
{
size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v___x_985_ = ((size_t)0ULL);
v___x_986_ = lean_usize_of_nat(v___x_982_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_960_, v_attrs_980_, v___x_985_, v___x_986_, v___x_983_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_a_973_ = v_a_988_;
goto v___jp_972_;
}
else
{
return v___x_987_;
}
}
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_b_964_);
return v___x_989_;
}
v___jp_972_:
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_962_, v___x_974_);
v_i_962_ = v___x_975_;
v_b_964_ = v_a_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_990_, lean_object* v_as_991_, lean_object* v_i_992_, lean_object* v_stop_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
size_t v_i_boxed_1002_; size_t v_stop_boxed_1003_; lean_object* v_res_1004_; 
v_i_boxed_1002_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_stop_boxed_1003_ = lean_unbox_usize(v_stop_993_);
lean_dec(v_stop_993_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_990_, v_as_991_, v_i_boxed_1002_, v_stop_boxed_1003_, v_b_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_as_991_);
lean_dec(v___x_990_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1005_, size_t v_i_1006_, lean_object* v_bs_1007_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_1006_, v_sz_1005_);
if (v___x_1008_ == 0)
{
return v_bs_1007_;
}
else
{
lean_object* v_v_1009_; lean_object* v_termination_1010_; lean_object* v_decreasingBy_x3f_1011_; lean_object* v___x_1012_; lean_object* v_bs_x27_1013_; size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v_v_1009_ = lean_array_uget_borrowed(v_bs_1007_, v_i_1006_);
v_termination_1010_ = lean_ctor_get(v_v_1009_, 8);
v_decreasingBy_x3f_1011_ = lean_ctor_get(v_termination_1010_, 4);
lean_inc(v_decreasingBy_x3f_1011_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v_bs_x27_1013_ = lean_array_uset(v_bs_1007_, v_i_1006_, v___x_1012_);
v___x_1014_ = ((size_t)1ULL);
v___x_1015_ = lean_usize_add(v_i_1006_, v___x_1014_);
v___x_1016_ = lean_array_uset(v_bs_x27_1013_, v_i_1006_, v_decreasingBy_x3f_1011_);
v_i_1006_ = v___x_1015_;
v_bs_1007_ = v___x_1016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_bs_1020_){
_start:
{
size_t v_sz_boxed_1021_; size_t v_i_boxed_1022_; lean_object* v_res_1023_; 
v_sz_boxed_1021_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1022_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1021_, v_i_boxed_1022_, v_bs_1020_);
return v_res_1023_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1024_; double v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_float_of_nat(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1028_, lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_ref_1035_; lean_object* v___x_1036_; lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1082_; 
v_ref_1035_ = lean_ctor_get(v___y_1032_, 2);
v___x_1036_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1082_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1082_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v_traceState_1042_; lean_object* v_env_1043_; lean_object* v_nextMacroScope_1044_; lean_object* v_ngen_1045_; lean_object* v_auxDeclNGen_1046_; lean_object* v_cache_1047_; lean_object* v_recordedDeps_1048_; lean_object* v_messages_1049_; lean_object* v_infoState_1050_; lean_object* v_snapshotTasks_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1081_; 
v___x_1041_ = lean_st_ref_take(v___y_1033_);
v_traceState_1042_ = lean_ctor_get(v___x_1041_, 4);
v_env_1043_ = lean_ctor_get(v___x_1041_, 0);
v_nextMacroScope_1044_ = lean_ctor_get(v___x_1041_, 1);
v_ngen_1045_ = lean_ctor_get(v___x_1041_, 2);
v_auxDeclNGen_1046_ = lean_ctor_get(v___x_1041_, 3);
v_cache_1047_ = lean_ctor_get(v___x_1041_, 5);
v_recordedDeps_1048_ = lean_ctor_get(v___x_1041_, 6);
v_messages_1049_ = lean_ctor_get(v___x_1041_, 7);
v_infoState_1050_ = lean_ctor_get(v___x_1041_, 8);
v_snapshotTasks_1051_ = lean_ctor_get(v___x_1041_, 9);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1053_ = v___x_1041_;
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snapshotTasks_1051_);
lean_inc(v_infoState_1050_);
lean_inc(v_messages_1049_);
lean_inc(v_recordedDeps_1048_);
lean_inc(v_cache_1047_);
lean_inc(v_traceState_1042_);
lean_inc(v_auxDeclNGen_1046_);
lean_inc(v_ngen_1045_);
lean_inc(v_nextMacroScope_1044_);
lean_inc(v_env_1043_);
lean_dec(v___x_1041_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint64_t v_tid_1055_; lean_object* v_traces_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1080_; 
v_tid_1055_ = lean_ctor_get_uint64(v_traceState_1042_, sizeof(void*)*1);
v_traces_1056_ = lean_ctor_get(v_traceState_1042_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_traceState_1042_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1058_ = v_traceState_1042_;
v_isShared_1059_ = v_isSharedCheck_1080_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_traces_1056_);
lean_dec(v_traceState_1042_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1080_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; double v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1063_ = 0;
v___x_1064_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1065_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1065_, 0, v_cls_1028_);
lean_ctor_set(v___x_1065_, 1, v___x_1061_);
lean_ctor_set(v___x_1065_, 2, v___x_1064_);
lean_ctor_set_float(v___x_1065_, sizeof(void*)*3, v___x_1062_);
lean_ctor_set_float(v___x_1065_, sizeof(void*)*3 + 8, v___x_1062_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*3 + 16, v___x_1063_);
v___x_1066_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1067_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v_a_1037_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
lean_inc(v_ref_1035_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_ref_1035_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_PersistentArray_push___redArg(v_traces_1056_, v___x_1068_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1069_);
v___x_1071_ = v___x_1058_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1069_);
lean_ctor_set_uint64(v_reuseFailAlloc_1079_, sizeof(void*)*1, v_tid_1055_);
v___x_1071_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v___x_1071_);
v___x_1073_ = v___x_1053_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_env_1043_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_nextMacroScope_1044_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_ngen_1045_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_auxDeclNGen_1046_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_cache_1047_);
lean_ctor_set(v_reuseFailAlloc_1078_, 6, v_recordedDeps_1048_);
lean_ctor_set(v_reuseFailAlloc_1078_, 7, v_messages_1049_);
lean_ctor_set(v_reuseFailAlloc_1078_, 8, v_infoState_1050_);
lean_ctor_set(v_reuseFailAlloc_1078_, 9, v_snapshotTasks_1051_);
v___x_1073_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_put(v___y_1033_, v___x_1073_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1060_);
v___x_1076_ = v___x_1039_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1060_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1083_, lean_object* v_msg_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1083_, v_msg_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_snd_1094_, size_t v_sz_1095_, size_t v___x_1096_, lean_object* v_a_1097_, lean_object* v_fst_1098_, lean_object* v_fixedArgs_1099_, lean_object* v_fst_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_wfRel_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v_a_1120_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v_toCold_1251_; lean_object* v_options_1252_; uint8_t v_hasTrace_1253_; 
v_toCold_1251_ = lean_ctor_get(v___y_1109_, 0);
v_options_1252_ = lean_ctor_get(v_toCold_1251_, 2);
v_hasTrace_1253_ = lean_ctor_get_uint8(v_options_1252_, sizeof(void*)*1);
if (v_hasTrace_1253_ == 0)
{
lean_dec(v___x_1103_);
v___y_1222_ = v___y_1105_;
v___y_1223_ = v___y_1106_;
v___y_1224_ = v___y_1107_;
v___y_1225_ = v___y_1108_;
v___y_1226_ = v___y_1109_;
v___y_1227_ = v___y_1110_;
goto v___jp_1221_;
}
else
{
lean_object* v_inheritedTraceOptions_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_inheritedTraceOptions_1254_ = lean_ctor_get(v_toCold_1251_, 11);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
lean_inc(v___x_1103_);
v___x_1256_ = l_Lean_Name_append(v___x_1255_, v___x_1103_);
v___x_1257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1254_, v_options_1252_, v___x_1256_);
lean_dec(v___x_1256_);
if (v___x_1257_ == 0)
{
lean_dec(v___x_1103_);
v___y_1222_ = v___y_1105_;
v___y_1223_ = v___y_1106_;
v___y_1224_ = v___y_1107_;
v___y_1225_ = v___y_1108_;
v___y_1226_ = v___y_1109_;
v___y_1227_ = v___y_1110_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1104_);
v___x_1259_ = l_Lean_MessageData_ofExpr(v_wfRel_1104_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1103_, v___x_1260_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_dec_ref_known(v___x_1261_, 1);
v___y_1222_ = v___y_1105_;
v___y_1223_ = v___y_1106_;
v___y_1224_ = v___y_1107_;
v___y_1225_ = v___y_1108_;
v___y_1226_ = v___y_1109_;
v___y_1227_ = v___y_1110_;
goto v___jp_1221_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_wfRel_1104_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_fst_1100_);
lean_dec_ref(v_fixedArgs_1099_);
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v_a_1097_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v___x_1121_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1114_, v___y_1117_, v___y_1115_);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 1);
lean_ctor_set(v___x_1123_, 0, v_a_1120_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
v___jp_1130_:
{
lean_object* v___x_1137_; lean_object* v_env_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_st_ref_get(v___y_1136_);
v_env_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1138_);
lean_dec(v___x_1137_);
v___x_1139_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1094_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1139_, 1);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1095_, v___x_1096_, v_a_1097_);
lean_inc_ref(v_fst_1098_);
v___x_1141_ = l_Lean_Elab_WF_mkFix(v_fst_1098_, v_fixedArgs_1099_, v_fst_1100_, v_wfRel_1104_, v___x_1101_, v___x_1140_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1142_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_st_ref_get(v___y_1136_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref_n(v_env_1146_, 2);
lean_dec(v___x_1145_);
v___x_1147_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1138_, v___y_1134_, v___y_1136_);
lean_dec_ref(v___x_1147_);
v___x_1148_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1146_, v_a_1144_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1209_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1209_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1209_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v_env_1154_; lean_object* v_nextMacroScope_1155_; lean_object* v_ngen_1156_; lean_object* v_auxDeclNGen_1157_; lean_object* v_traceState_1158_; lean_object* v_recordedDeps_1159_; lean_object* v_messages_1160_; lean_object* v_infoState_1161_; lean_object* v_snapshotTasks_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1207_; 
v___x_1153_ = lean_st_ref_take(v___y_1136_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
v_nextMacroScope_1155_ = lean_ctor_get(v___x_1153_, 1);
v_ngen_1156_ = lean_ctor_get(v___x_1153_, 2);
v_auxDeclNGen_1157_ = lean_ctor_get(v___x_1153_, 3);
v_traceState_1158_ = lean_ctor_get(v___x_1153_, 4);
v_recordedDeps_1159_ = lean_ctor_get(v___x_1153_, 6);
v_messages_1160_ = lean_ctor_get(v___x_1153_, 7);
v_infoState_1161_ = lean_ctor_get(v___x_1153_, 8);
v_snapshotTasks_1162_ = lean_ctor_get(v___x_1153_, 9);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1153_, 5);
lean_dec(v_unused_1208_);
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1207_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snapshotTasks_1162_);
lean_inc(v_infoState_1161_);
lean_inc(v_messages_1160_);
lean_inc(v_recordedDeps_1159_);
lean_inc(v_traceState_1158_);
lean_inc(v_auxDeclNGen_1157_);
lean_inc(v_ngen_1156_);
lean_inc(v_nextMacroScope_1155_);
lean_inc(v_env_1154_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1207_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = l_Lean_copyExtraModUses(v_env_1146_, v_env_1154_);
v___x_1167_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 5, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_nextMacroScope_1155_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_ngen_1156_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_auxDeclNGen_1157_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_traceState_1158_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_recordedDeps_1159_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_messages_1160_);
lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_infoState_1161_);
lean_ctor_set(v_reuseFailAlloc_1206_, 9, v_snapshotTasks_1162_);
v___x_1169_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_mctx_1172_; lean_object* v_zetaDeltaFVarIds_1173_; lean_object* v_postponed_1174_; lean_object* v_diag_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1204_; 
v___x_1170_ = lean_st_ref_put(v___y_1136_, v___x_1169_);
v___x_1171_ = lean_st_ref_take(v___y_1134_);
v_mctx_1172_ = lean_ctor_get(v___x_1171_, 0);
v_zetaDeltaFVarIds_1173_ = lean_ctor_get(v___x_1171_, 2);
v_postponed_1174_ = lean_ctor_get(v___x_1171_, 3);
v_diag_1175_ = lean_ctor_get(v___x_1171_, 4);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v___x_1171_, 1);
lean_dec(v_unused_1205_);
v___x_1177_ = v___x_1171_;
v_isShared_1178_ = v_isSharedCheck_1204_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_diag_1175_);
lean_inc(v_postponed_1174_);
lean_inc(v_zetaDeltaFVarIds_1173_);
lean_inc(v_mctx_1172_);
lean_dec(v___x_1171_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1204_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_mctx_1172_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_zetaDeltaFVarIds_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_postponed_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_diag_1175_);
v___x_1181_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v_ref_1183_; uint8_t v_kind_1184_; lean_object* v_levelParams_1185_; lean_object* v_modifiers_1186_; lean_object* v_declName_1187_; lean_object* v_binders_1188_; lean_object* v_numSectionVars_1189_; lean_object* v_type_1190_; lean_object* v_termination_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v___x_1182_ = lean_st_ref_put(v___y_1134_, v___x_1181_);
v_ref_1183_ = lean_ctor_get(v_fst_1098_, 0);
v_kind_1184_ = lean_ctor_get_uint8(v_fst_1098_, sizeof(void*)*9);
v_levelParams_1185_ = lean_ctor_get(v_fst_1098_, 1);
v_modifiers_1186_ = lean_ctor_get(v_fst_1098_, 2);
v_declName_1187_ = lean_ctor_get(v_fst_1098_, 3);
v_binders_1188_ = lean_ctor_get(v_fst_1098_, 4);
v_numSectionVars_1189_ = lean_ctor_get(v_fst_1098_, 5);
v_type_1190_ = lean_ctor_get(v_fst_1098_, 6);
v_termination_1191_ = lean_ctor_get(v_fst_1098_, 8);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_fst_1098_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_fst_1098_, 7);
lean_dec(v_unused_1202_);
v___x_1193_ = v_fst_1098_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_termination_1191_);
lean_inc(v_type_1190_);
lean_inc(v_numSectionVars_1189_);
lean_inc(v_binders_1188_);
lean_inc(v_declName_1187_);
lean_inc(v_modifiers_1186_);
lean_inc(v_levelParams_1185_);
lean_inc(v_ref_1183_);
lean_dec(v_fst_1098_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 7, v_a_1149_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_ref_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_levelParams_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_modifiers_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_declName_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_binders_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_numSectionVars_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_type_1190_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_a_1149_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_termination_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*9, v_kind_1184_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1196_);
v___x_1198_ = v___x_1151_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
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
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_env_1146_);
lean_dec_ref(v_fst_1098_);
v_a_1210_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1148_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1148_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; 
lean_dec_ref(v_fst_1098_);
v_a_1218_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1143_, 1);
v___y_1113_ = v___y_1132_;
v___y_1114_ = v_env_1138_;
v___y_1115_ = v___y_1136_;
v___y_1116_ = v___y_1135_;
v___y_1117_ = v___y_1134_;
v___y_1118_ = v___y_1131_;
v___y_1119_ = v___y_1133_;
v_a_1120_ = v_a_1218_;
goto v___jp_1112_;
}
}
else
{
lean_object* v_a_1219_; 
lean_dec_ref(v_fst_1098_);
v_a_1219_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1141_, 1);
v___y_1113_ = v___y_1132_;
v___y_1114_ = v_env_1138_;
v___y_1115_ = v___y_1136_;
v___y_1116_ = v___y_1135_;
v___y_1117_ = v___y_1134_;
v___y_1118_ = v___y_1131_;
v___y_1119_ = v___y_1133_;
v_a_1120_ = v_a_1219_;
goto v___jp_1112_;
}
}
else
{
lean_object* v_a_1220_; 
lean_dec_ref(v_wfRel_1104_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_fst_1100_);
lean_dec_ref(v_fixedArgs_1099_);
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v_a_1097_);
v_a_1220_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1139_, 1);
v___y_1113_ = v___y_1132_;
v___y_1114_ = v_env_1138_;
v___y_1115_ = v___y_1136_;
v___y_1116_ = v___y_1135_;
v___y_1117_ = v___y_1134_;
v___y_1118_ = v___y_1131_;
v___y_1119_ = v___y_1133_;
v_a_1120_ = v_a_1220_;
goto v___jp_1112_;
}
}
v___jp_1221_:
{
lean_object* v___x_1228_; 
lean_inc_ref(v_wfRel_1104_);
v___x_1228_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1104_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
if (lean_obj_tag(v_a_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_array_get_size(v_a_1097_);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
v___y_1131_ = v___y_1222_;
v___y_1132_ = v___y_1223_;
v___y_1133_ = v___y_1224_;
v___y_1134_ = v___y_1225_;
v___y_1135_ = v___y_1226_;
v___y_1136_ = v___y_1227_;
goto v___jp_1130_;
}
else
{
size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_usize_of_nat(v___x_1231_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1231_, v_a_1097_, v___x_1096_, v___x_1233_, v___x_1102_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec_ref_known(v___x_1234_, 1);
v___y_1131_ = v___y_1222_;
v___y_1132_ = v___y_1223_;
v___y_1133_ = v___y_1224_;
v___y_1134_ = v___y_1225_;
v___y_1135_ = v___y_1226_;
v___y_1136_ = v___y_1227_;
goto v___jp_1130_;
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v_wfRel_1104_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_fst_1100_);
lean_dec_ref(v_fixedArgs_1099_);
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v_a_1097_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_1229_, 1);
v___y_1131_ = v___y_1222_;
v___y_1132_ = v___y_1223_;
v___y_1133_ = v___y_1224_;
v___y_1134_ = v___y_1225_;
v___y_1135_ = v___y_1226_;
v___y_1136_ = v___y_1227_;
goto v___jp_1130_;
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_wfRel_1104_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_fst_1100_);
lean_dec_ref(v_fixedArgs_1099_);
lean_dec_ref(v_fst_1098_);
lean_dec_ref(v_a_1097_);
v_a_1243_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1228_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1228_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_snd_1270_ = _args[0];
lean_object* v_sz_1271_ = _args[1];
lean_object* v___x_1272_ = _args[2];
lean_object* v_a_1273_ = _args[3];
lean_object* v_fst_1274_ = _args[4];
lean_object* v_fixedArgs_1275_ = _args[5];
lean_object* v_fst_1276_ = _args[6];
lean_object* v___x_1277_ = _args[7];
lean_object* v___x_1278_ = _args[8];
lean_object* v___x_1279_ = _args[9];
lean_object* v_wfRel_1280_ = _args[10];
lean_object* v___y_1281_ = _args[11];
lean_object* v___y_1282_ = _args[12];
lean_object* v___y_1283_ = _args[13];
lean_object* v___y_1284_ = _args[14];
lean_object* v___y_1285_ = _args[15];
lean_object* v___y_1286_ = _args[16];
lean_object* v___y_1287_ = _args[17];
_start:
{
size_t v_sz_boxed_1288_; size_t v___x_44944__boxed_1289_; lean_object* v_res_1290_; 
v_sz_boxed_1288_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v___x_44944__boxed_1289_ = lean_unbox_usize(v___x_1272_);
lean_dec(v___x_1272_);
v_res_1290_ = l_Lean_Elab_wfRecursion___lam__3(v_snd_1270_, v_sz_boxed_1288_, v___x_44944__boxed_1289_, v_a_1273_, v_fst_1274_, v_fixedArgs_1275_, v_fst_1276_, v___x_1277_, v___x_1278_, v___x_1279_, v_wfRel_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v_snd_1270_);
return v_res_1290_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1294_, size_t v___x_1295_, lean_object* v_a_1296_, lean_object* v_snd_1297_, lean_object* v_fst_1298_, lean_object* v_fst_1299_, lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v_declName_1302_, lean_object* v_fst_1303_, lean_object* v_wf_1304_, lean_object* v_fixedArgs_1305_, lean_object* v_type_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_whnfForall(v_type_1306_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; uint8_t v___x_1329_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1329_ = l_Lean_Expr_isForall(v_a_1315_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_fixedArgs_1305_);
lean_dec_ref(v_wf_1304_);
lean_dec_ref(v_fst_1303_);
lean_dec(v_declName_1302_);
lean_dec(v___x_1301_);
lean_dec_ref(v_fst_1299_);
lean_dec_ref(v_fst_1298_);
lean_dec_ref(v_snd_1297_);
lean_dec_ref(v_a_1296_);
v___x_1330_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1331_ = l_Lean_MessageData_ofExpr(v_a_1315_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1332_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
v___y_1317_ = v___y_1307_;
v___y_1318_ = v___y_1308_;
v___y_1319_ = v___y_1309_;
v___y_1320_ = v___y_1310_;
v___y_1321_ = v___y_1311_;
v___y_1322_ = v___y_1312_;
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___x_1323_ = l_Lean_Expr_bindingDomain_x21(v_a_1315_);
lean_dec(v_a_1315_);
lean_inc_ref(v_a_1296_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_1294_, v___x_1295_, v_a_1296_);
v___x_1325_ = lean_box_usize(v_sz_1294_);
v___x_1326_ = lean_box_usize(v___x_1295_);
lean_inc_ref(v___x_1324_);
lean_inc_ref(v_fst_1299_);
lean_inc_ref(v_fixedArgs_1305_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1327_, 0, v_snd_1297_);
lean_closure_set(v___f_1327_, 1, v___x_1325_);
lean_closure_set(v___f_1327_, 2, v___x_1326_);
lean_closure_set(v___f_1327_, 3, v_a_1296_);
lean_closure_set(v___f_1327_, 4, v_fst_1298_);
lean_closure_set(v___f_1327_, 5, v_fixedArgs_1305_);
lean_closure_set(v___f_1327_, 6, v_fst_1299_);
lean_closure_set(v___f_1327_, 7, v___x_1324_);
lean_closure_set(v___f_1327_, 8, v___x_1300_);
lean_closure_set(v___f_1327_, 9, v___x_1301_);
v___x_1328_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1324_, v_declName_1302_, v_fst_1303_, v_fixedArgs_1305_, v_fst_1299_, v___x_1323_, v_wf_1304_, v___f_1327_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v___x_1328_;
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_fixedArgs_1305_);
lean_dec_ref(v_wf_1304_);
lean_dec_ref(v_fst_1303_);
lean_dec(v_declName_1302_);
lean_dec(v___x_1301_);
lean_dec_ref(v_fst_1299_);
lean_dec_ref(v_fst_1298_);
lean_dec_ref(v_snd_1297_);
lean_dec_ref(v_a_1296_);
v_a_1342_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1314_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1314_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1350_ = _args[0];
lean_object* v___x_1351_ = _args[1];
lean_object* v_a_1352_ = _args[2];
lean_object* v_snd_1353_ = _args[3];
lean_object* v_fst_1354_ = _args[4];
lean_object* v_fst_1355_ = _args[5];
lean_object* v___x_1356_ = _args[6];
lean_object* v___x_1357_ = _args[7];
lean_object* v_declName_1358_ = _args[8];
lean_object* v_fst_1359_ = _args[9];
lean_object* v_wf_1360_ = _args[10];
lean_object* v_fixedArgs_1361_ = _args[11];
lean_object* v_type_1362_ = _args[12];
lean_object* v___y_1363_ = _args[13];
lean_object* v___y_1364_ = _args[14];
lean_object* v___y_1365_ = _args[15];
lean_object* v___y_1366_ = _args[16];
lean_object* v___y_1367_ = _args[17];
lean_object* v___y_1368_ = _args[18];
lean_object* v___y_1369_ = _args[19];
_start:
{
size_t v_sz_boxed_1370_; size_t v___x_45265__boxed_1371_; lean_object* v_res_1372_; 
v_sz_boxed_1370_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v___x_45265__boxed_1371_ = lean_unbox_usize(v___x_1351_);
lean_dec(v___x_1351_);
v_res_1372_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1370_, v___x_45265__boxed_1371_, v_a_1352_, v_snd_1353_, v_fst_1354_, v_fst_1355_, v___x_1356_, v___x_1357_, v_declName_1358_, v_fst_1359_, v_wf_1360_, v_fixedArgs_1361_, v_type_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1373_, lean_object* v_fst_1374_, lean_object* v_fst_1375_, lean_object* v_fst_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Elab_WF_guessLex(v_a_1373_, v_fst_1374_, v_fst_1375_, v_fst_1376_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1385_, lean_object* v_fst_1386_, lean_object* v_fst_1387_, lean_object* v_fst_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1385_, v_fst_1386_, v_fst_1387_, v_fst_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_env_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_env_1407_; lean_object* v_a_1409_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1406_ = lean_st_ref_get(v___y_1404_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v___x_1419_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1397_, v___y_1402_, v___y_1404_);
lean_dec_ref(v___x_1419_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_1420_ = lean_apply_7(v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, lean_box(0));
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1407_, v___y_1402_, v___y_1404_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_a_1421_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1421_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; 
v_a_1431_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1420_, 1);
v_a_1409_ = v_a_1431_;
goto v___jp_1408_;
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v___x_1410_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1407_, v___y_1402_, v___y_1404_);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1418_);
v___x_1412_ = v___x_1410_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v___x_1410_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
lean_ctor_set(v___x_1412_, 0, v_a_1409_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1409_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_env_1432_, lean_object* v_x_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1432_, v_x_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1442_, uint8_t v_isExporting_1443_, lean_object* v___x_1444_, lean_object* v___y_1445_, lean_object* v___x_1446_, lean_object* v_a_x3f_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_env_1450_; lean_object* v_nextMacroScope_1451_; lean_object* v_ngen_1452_; lean_object* v_auxDeclNGen_1453_; lean_object* v_traceState_1454_; lean_object* v_recordedDeps_1455_; lean_object* v_messages_1456_; lean_object* v_infoState_1457_; lean_object* v_snapshotTasks_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1483_; 
v___x_1449_ = lean_st_ref_take(v___y_1442_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
v_nextMacroScope_1451_ = lean_ctor_get(v___x_1449_, 1);
v_ngen_1452_ = lean_ctor_get(v___x_1449_, 2);
v_auxDeclNGen_1453_ = lean_ctor_get(v___x_1449_, 3);
v_traceState_1454_ = lean_ctor_get(v___x_1449_, 4);
v_recordedDeps_1455_ = lean_ctor_get(v___x_1449_, 6);
v_messages_1456_ = lean_ctor_get(v___x_1449_, 7);
v_infoState_1457_ = lean_ctor_get(v___x_1449_, 8);
v_snapshotTasks_1458_ = lean_ctor_get(v___x_1449_, 9);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v___x_1449_, 5);
lean_dec(v_unused_1484_);
v___x_1460_ = v___x_1449_;
v_isShared_1461_ = v_isSharedCheck_1483_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_snapshotTasks_1458_);
lean_inc(v_infoState_1457_);
lean_inc(v_messages_1456_);
lean_inc(v_recordedDeps_1455_);
lean_inc(v_traceState_1454_);
lean_inc(v_auxDeclNGen_1453_);
lean_inc(v_ngen_1452_);
lean_inc(v_nextMacroScope_1451_);
lean_inc(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1483_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = l_Lean_Environment_setExporting(v_env_1450_, v_isExporting_1443_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 5, v___x_1444_);
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_nextMacroScope_1451_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_ngen_1452_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_auxDeclNGen_1453_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_traceState_1454_);
lean_ctor_set(v_reuseFailAlloc_1482_, 5, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1482_, 6, v_recordedDeps_1455_);
lean_ctor_set(v_reuseFailAlloc_1482_, 7, v_messages_1456_);
lean_ctor_set(v_reuseFailAlloc_1482_, 8, v_infoState_1457_);
lean_ctor_set(v_reuseFailAlloc_1482_, 9, v_snapshotTasks_1458_);
v___x_1464_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_mctx_1467_; lean_object* v_zetaDeltaFVarIds_1468_; lean_object* v_postponed_1469_; lean_object* v_diag_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v___x_1465_ = lean_st_ref_put(v___y_1442_, v___x_1464_);
v___x_1466_ = lean_st_ref_take(v___y_1445_);
v_mctx_1467_ = lean_ctor_get(v___x_1466_, 0);
v_zetaDeltaFVarIds_1468_ = lean_ctor_get(v___x_1466_, 2);
v_postponed_1469_ = lean_ctor_get(v___x_1466_, 3);
v_diag_1470_ = lean_ctor_get(v___x_1466_, 4);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1466_, 1);
lean_dec(v_unused_1481_);
v___x_1472_ = v___x_1466_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_diag_1470_);
lean_inc(v_postponed_1469_);
lean_inc(v_zetaDeltaFVarIds_1468_);
lean_inc(v_mctx_1467_);
lean_dec(v___x_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1446_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_mctx_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_zetaDeltaFVarIds_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_postponed_1469_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_diag_1470_);
v___x_1476_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_st_ref_put(v___y_1445_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1474_);
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1485_, lean_object* v_isExporting_1486_, lean_object* v___x_1487_, lean_object* v___y_1488_, lean_object* v___x_1489_, lean_object* v_a_x3f_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_isExporting_boxed_1492_; lean_object* v_res_1493_; 
v_isExporting_boxed_1492_ = lean_unbox(v_isExporting_1486_);
v_res_1493_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1485_, v_isExporting_boxed_1492_, v___x_1487_, v___y_1488_, v___x_1489_, v_a_x3f_1490_);
lean_dec(v_a_x3f_1490_);
lean_dec(v___y_1488_);
lean_dec(v___y_1485_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1494_, uint8_t v_isExporting_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v_env_1504_; lean_object* v___x_1505_; uint8_t v_isModule_1506_; 
v___x_1503_ = lean_st_ref_get(v___y_1501_);
v_env_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_ref(v_env_1504_);
lean_dec(v___x_1503_);
v___x_1505_ = l_Lean_Environment_header(v_env_1504_);
v_isModule_1506_ = lean_ctor_get_uint8(v___x_1505_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1505_);
if (v_isModule_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref(v_env_1504_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v___x_1507_ = lean_apply_7(v_x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
return v___x_1507_;
}
else
{
uint8_t v_isExporting_1508_; 
v_isExporting_1508_ = lean_ctor_get_uint8(v_env_1504_, sizeof(void*)*13);
lean_dec_ref(v_env_1504_);
if (v_isExporting_1495_ == 0)
{
if (v_isExporting_1508_ == 0)
{
lean_object* v___x_1575_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v___x_1575_ = lean_apply_7(v_x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
return v___x_1575_;
}
else
{
goto v___jp_1509_;
}
}
else
{
if (v_isExporting_1508_ == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1576_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v___x_1576_ = lean_apply_7(v_x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
return v___x_1576_;
}
}
v___jp_1509_:
{
lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v_nextMacroScope_1512_; lean_object* v_ngen_1513_; lean_object* v_auxDeclNGen_1514_; lean_object* v_traceState_1515_; lean_object* v_recordedDeps_1516_; lean_object* v_messages_1517_; lean_object* v_infoState_1518_; lean_object* v_snapshotTasks_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1573_; 
v___x_1510_ = lean_st_ref_take(v___y_1501_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
v_nextMacroScope_1512_ = lean_ctor_get(v___x_1510_, 1);
v_ngen_1513_ = lean_ctor_get(v___x_1510_, 2);
v_auxDeclNGen_1514_ = lean_ctor_get(v___x_1510_, 3);
v_traceState_1515_ = lean_ctor_get(v___x_1510_, 4);
v_recordedDeps_1516_ = lean_ctor_get(v___x_1510_, 6);
v_messages_1517_ = lean_ctor_get(v___x_1510_, 7);
v_infoState_1518_ = lean_ctor_get(v___x_1510_, 8);
v_snapshotTasks_1519_ = lean_ctor_get(v___x_1510_, 9);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1510_, 5);
lean_dec(v_unused_1574_);
v___x_1521_ = v___x_1510_;
v_isShared_1522_ = v_isSharedCheck_1573_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snapshotTasks_1519_);
lean_inc(v_infoState_1518_);
lean_inc(v_messages_1517_);
lean_inc(v_recordedDeps_1516_);
lean_inc(v_traceState_1515_);
lean_inc(v_auxDeclNGen_1514_);
lean_inc(v_ngen_1513_);
lean_inc(v_nextMacroScope_1512_);
lean_inc(v_env_1511_);
lean_dec(v___x_1510_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1573_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = l_Lean_Environment_setExporting(v_env_1511_, v_isExporting_1495_);
v___x_1524_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 5, v___x_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_nextMacroScope_1512_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_ngen_1513_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_auxDeclNGen_1514_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_traceState_1515_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v_recordedDeps_1516_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v_messages_1517_);
lean_ctor_set(v_reuseFailAlloc_1572_, 8, v_infoState_1518_);
lean_ctor_set(v_reuseFailAlloc_1572_, 9, v_snapshotTasks_1519_);
v___x_1526_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_mctx_1529_; lean_object* v_zetaDeltaFVarIds_1530_; lean_object* v_postponed_1531_; lean_object* v_diag_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1570_; 
v___x_1527_ = lean_st_ref_put(v___y_1501_, v___x_1526_);
v___x_1528_ = lean_st_ref_take(v___y_1499_);
v_mctx_1529_ = lean_ctor_get(v___x_1528_, 0);
v_zetaDeltaFVarIds_1530_ = lean_ctor_get(v___x_1528_, 2);
v_postponed_1531_ = lean_ctor_get(v___x_1528_, 3);
v_diag_1532_ = lean_ctor_get(v___x_1528_, 4);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___x_1528_, 1);
lean_dec(v_unused_1571_);
v___x_1534_ = v___x_1528_;
v_isShared_1535_ = v_isSharedCheck_1570_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_diag_1532_);
lean_inc(v_postponed_1531_);
lean_inc(v_zetaDeltaFVarIds_1530_);
lean_inc(v_mctx_1529_);
lean_dec(v___x_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1570_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v___x_1536_);
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_mctx_1529_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_zetaDeltaFVarIds_1530_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_postponed_1531_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_diag_1532_);
v___x_1538_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v_r_1540_; 
v___x_1539_ = lean_st_ref_put(v___y_1499_, v___x_1538_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
v_r_1540_ = lean_apply_7(v_x_1494_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, lean_box(0));
if (lean_obj_tag(v_r_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1557_; 
v_a_1541_ = lean_ctor_get(v_r_1540_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_r_1540_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1543_ = v_r_1540_;
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v_r_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1557_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
lean_inc(v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v___x_1547_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1501_, v_isExporting_1508_, v___x_1524_, v___y_1499_, v___x_1536_, v___x_1546_);
lean_dec_ref(v___x_1546_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1555_);
v___x_1549_ = v___x_1547_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v___x_1547_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1541_);
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1541_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1558_ = lean_ctor_get(v_r_1540_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v_r_1540_, 1);
v___x_1559_ = lean_box(0);
v___x_1560_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1501_, v_isExporting_1508_, v___x_1524_, v___y_1499_, v___x_1536_, v___x_1559_);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1568_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 1);
lean_ctor_set(v___x_1562_, 0, v_a_1558_);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1558_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1577_, lean_object* v_isExporting_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v_isExporting_boxed_1586_; lean_object* v_res_1587_; 
v_isExporting_boxed_1586_ = lean_unbox(v_isExporting_1578_);
v_res_1587_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1577_, v_isExporting_boxed_1586_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1588_, uint8_t v_when_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
if (v_when_1589_ == 0)
{
lean_object* v___x_1597_; 
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
v___x_1597_ = lean_apply_7(v_x_1588_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, lean_box(0));
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = 0;
v___x_1599_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1588_, v___x_1598_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1600_, lean_object* v_when_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_when_boxed_1609_; lean_object* v_res_1610_; 
v_when_boxed_1609_ = lean_unbox(v_when_1601_);
v_res_1610_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1600_, v_when_boxed_1609_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t v_sz_1611_, size_t v_i_1612_, lean_object* v_bs_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_lt(v_i_1612_, v_sz_1611_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_bs_1613_);
return v___x_1618_;
}
else
{
lean_object* v_v_1619_; lean_object* v_ref_1620_; uint8_t v_kind_1621_; lean_object* v_levelParams_1622_; lean_object* v_modifiers_1623_; lean_object* v_declName_1624_; lean_object* v_binders_1625_; lean_object* v_numSectionVars_1626_; lean_object* v_type_1627_; lean_object* v_value_1628_; lean_object* v_termination_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1652_; 
v_v_1619_ = lean_array_uget(v_bs_1613_, v_i_1612_);
v_ref_1620_ = lean_ctor_get(v_v_1619_, 0);
v_kind_1621_ = lean_ctor_get_uint8(v_v_1619_, sizeof(void*)*9);
v_levelParams_1622_ = lean_ctor_get(v_v_1619_, 1);
v_modifiers_1623_ = lean_ctor_get(v_v_1619_, 2);
v_declName_1624_ = lean_ctor_get(v_v_1619_, 3);
v_binders_1625_ = lean_ctor_get(v_v_1619_, 4);
v_numSectionVars_1626_ = lean_ctor_get(v_v_1619_, 5);
v_type_1627_ = lean_ctor_get(v_v_1619_, 6);
v_value_1628_ = lean_ctor_get(v_v_1619_, 7);
v_termination_1629_ = lean_ctor_get(v_v_1619_, 8);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_v_1619_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1631_ = v_v_1619_;
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_termination_1629_);
lean_inc(v_value_1628_);
lean_inc(v_type_1627_);
lean_inc(v_numSectionVars_1626_);
lean_inc(v_binders_1625_);
lean_inc(v_declName_1624_);
lean_inc(v_modifiers_1623_);
lean_inc(v_levelParams_1622_);
lean_inc(v_ref_1620_);
lean_dec(v_v_1619_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v_bs_x27_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v_bs_x27_1634_ = lean_array_uset(v_bs_1613_, v_i_1612_, v___x_1633_);
v___x_1635_ = l_Lean_Elab_WF_floatRecApp(v_value_1628_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 7, v_a_1636_);
v___x_1638_ = v___x_1631_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_ref_1620_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_levelParams_1622_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_modifiers_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_declName_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_binders_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v_numSectionVars_1626_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_type_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_a_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_termination_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, sizeof(void*)*9, v_kind_1621_);
v___x_1638_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_add(v_i_1612_, v___x_1639_);
v___x_1641_ = lean_array_uset(v_bs_x27_1634_, v_i_1612_, v___x_1638_);
v_i_1612_ = v___x_1640_;
v_bs_1613_ = v___x_1641_;
goto _start;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v_bs_x27_1634_);
lean_del_object(v___x_1631_);
lean_dec_ref(v_termination_1629_);
lean_dec_ref(v_type_1627_);
lean_dec(v_numSectionVars_1626_);
lean_dec(v_binders_1625_);
lean_dec(v_declName_1624_);
lean_dec_ref(v_modifiers_1623_);
lean_dec(v_levelParams_1622_);
lean_dec(v_ref_1620_);
v_a_1644_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1635_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1635_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_sz_1653_, lean_object* v_i_1654_, lean_object* v_bs_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
size_t v_sz_boxed_1659_; size_t v_i_boxed_1660_; lean_object* v_res_1661_; 
v_sz_boxed_1659_ = lean_unbox_usize(v_sz_1653_);
lean_dec(v_sz_1653_);
v_i_boxed_1660_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_boxed_1659_, v_i_boxed_1660_, v_bs_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_1662_, size_t v_i_1663_, lean_object* v_bs_1664_){
_start:
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_usize_dec_lt(v_i_1663_, v_sz_1662_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_bs_1664_);
return v___x_1666_;
}
else
{
lean_object* v_v_1667_; 
v_v_1667_ = lean_array_uget_borrowed(v_bs_1664_, v_i_1663_);
if (lean_obj_tag(v_v_1667_) == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref(v_bs_1664_);
v___x_1668_ = lean_box(0);
return v___x_1668_;
}
else
{
lean_object* v_val_1669_; lean_object* v___x_1670_; lean_object* v_bs_x27_1671_; size_t v___x_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v_val_1669_ = lean_ctor_get(v_v_1667_, 0);
lean_inc(v_val_1669_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v_bs_x27_1671_ = lean_array_uset(v_bs_1664_, v_i_1663_, v___x_1670_);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1663_, v___x_1672_);
v___x_1674_ = lean_array_uset(v_bs_x27_1671_, v_i_1663_, v_val_1669_);
v_i_1663_ = v___x_1673_;
v_bs_1664_ = v___x_1674_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_1676_, lean_object* v_i_1677_, lean_object* v_bs_1678_){
_start:
{
size_t v_sz_boxed_1679_; size_t v_i_boxed_1680_; lean_object* v_res_1681_; 
v_sz_boxed_1679_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1680_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_1679_, v_i_boxed_1680_, v_bs_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_bs_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_bs_1684_);
return v___x_1691_;
}
else
{
uint8_t v___x_1692_; lean_object* v_v_1693_; lean_object* v___x_1694_; lean_object* v_bs_x27_1695_; lean_object* v___x_1696_; 
v___x_1692_ = 0;
v_v_1693_ = lean_array_uget(v_bs_1684_, v_i_1683_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v_bs_x27_1695_ = lean_array_uset(v_bs_1684_, v_i_1683_, v___x_1694_);
v___x_1696_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1693_, v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1683_, v___x_1698_);
v___x_1700_ = lean_array_uset(v_bs_x27_1695_, v_i_1683_, v_a_1697_);
v_i_1683_ = v___x_1699_;
v_bs_1684_ = v___x_1700_;
goto _start;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_bs_x27_1695_);
v_a_1702_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1696_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1696_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1721_, lean_object* v_as_1722_, size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_b_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_a_1732_; uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec(v___x_1721_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_b_1725_);
return v___x_1737_;
}
else
{
lean_object* v_a_1738_; uint8_t v_kind_1739_; lean_object* v_declName_1740_; lean_object* v_type_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_a_1738_ = lean_array_uget_borrowed(v_as_1722_, v_i_1724_);
v_kind_1739_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*9);
v_declName_1740_ = lean_ctor_get(v_a_1738_, 3);
v_type_1741_ = lean_ctor_get(v_a_1738_, 6);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_name_eq(v_declName_1740_, v___x_1721_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1739_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_inc_ref(v_type_1741_);
v___x_1745_ = l_Lean_Meta_isProp(v_type_1741_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; uint8_t v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = lean_unbox(v_a_1746_);
lean_dec(v_a_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_inc(v___x_1721_);
lean_inc(v_a_1738_);
v___x_1748_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1738_, v___x_1721_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref_known(v___x_1748_, 1);
v_a_1732_ = v___x_1742_;
goto v___jp_1731_;
}
else
{
lean_dec(v___x_1721_);
return v___x_1748_;
}
}
else
{
v_a_1732_ = v___x_1742_;
goto v___jp_1731_;
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v___x_1721_);
v_a_1749_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1745_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1745_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
v_a_1732_ = v___x_1742_;
goto v___jp_1731_;
}
}
else
{
v_a_1732_ = v___x_1742_;
goto v___jp_1731_;
}
}
v___jp_1731_:
{
size_t v___x_1733_; size_t v___x_1734_; 
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1724_, v___x_1733_);
v_i_1724_ = v___x_1734_;
v_b_1725_ = v_a_1732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1757_, lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1757_, v_as_1758_, v_sz_boxed_1767_, v_i_boxed_1768_, v_b_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_as_1758_);
return v_res_1769_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1790_, lean_object* v_preDefs_1791_, lean_object* v_termMeasure_x3fs_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v_termMeasures_x3f_1803_; size_t v_sz_1804_; lean_object* v___x_1805_; 
v___x_1800_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_1801_ = lean_array_size(v_termMeasure_x3fs_1792_);
v___x_1802_ = ((size_t)0ULL);
v_termMeasures_x3f_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1801_, v___x_1802_, v_termMeasure_x3fs_1792_);
v_sz_1804_ = lean_array_size(v_preDefs_1791_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1804_, v___x_1802_, v_preDefs_1791_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; size_t v_sz_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v_env_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_n(v_a_1806_, 2);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = lean_box(0);
v_sz_1821_ = lean_array_size(v_a_1806_);
v___x_1822_ = lean_box_usize(v_sz_1821_);
v___x_1823_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1824_, 0, v_a_1806_);
lean_closure_set(v___f_1824_, 1, v___x_1822_);
lean_closure_set(v___f_1824_, 2, v___x_1823_);
lean_closure_set(v___f_1824_, 3, v___x_1807_);
lean_closure_set(v___f_1824_, 4, v___x_1800_);
v___x_1825_ = lean_st_ref_get(v_a_1798_);
v_env_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_env_1826_);
lean_dec(v___x_1825_);
v___x_1827_ = l_Lean_Environment_unlockAsync(v_env_1826_);
v___x_1828_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1827_, v___f_1824_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v_snd_1830_; lean_object* v_fst_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_2016_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v_snd_1830_ = lean_ctor_get(v_a_1829_, 1);
v_fst_1831_ = lean_ctor_get(v_a_1829_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1833_ = v_a_1829_;
v_isShared_1834_ = v_isSharedCheck_2016_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1831_);
lean_dec(v_a_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_2016_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_2015_; 
v_fst_1835_ = lean_ctor_get(v_snd_1830_, 0);
v_snd_1836_ = lean_ctor_get(v_snd_1830_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_snd_1830_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1838_ = v_snd_1830_;
v_isShared_1839_ = v_isSharedCheck_2015_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_snd_1836_);
lean_inc(v_fst_1835_);
lean_dec(v_snd_1830_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_2015_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_wf_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___x_2006_; lean_object* v_a_2007_; uint8_t v___x_2008_; 
lean_inc(v_snd_1836_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1899_, 0, v_snd_1836_);
v___x_1900_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2006_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1900_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = lean_unbox(v_a_2007_);
lean_dec(v_a_2007_);
if (v___x_2008_ == 0)
{
v___y_1969_ = v_a_1793_;
v___y_1970_ = v_a_1794_;
v___y_1971_ = v_a_1795_;
v___y_1972_ = v_a_1796_;
v___y_1973_ = v_a_1797_;
v___y_1974_ = v_a_1798_;
goto v___jp_1968_;
}
else
{
lean_object* v_value_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_value_2009_ = lean_ctor_get(v_snd_1836_, 7);
v___x_2010_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2009_);
v___x_2011_ = l_Lean_MessageData_ofExpr(v_value_2009_);
v___x_2012_ = l_Lean_indentD(v___x_2011_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2010_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1900_, v___x_2013_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
v___y_1969_ = v_a_1793_;
v___y_1970_ = v_a_1794_;
v___y_1971_ = v_a_1795_;
v___y_1972_ = v_a_1796_;
v___y_1973_ = v_a_1797_;
v___y_1974_ = v_a_1798_;
goto v___jp_1968_;
}
else
{
lean_dec_ref(v___f_1899_);
lean_del_object(v___x_1838_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec(v_termMeasures_x3f_1803_);
lean_dec_ref(v_docCtx_1790_);
return v___x_2014_;
}
}
v___jp_1840_:
{
lean_object* v___x_1850_; 
lean_inc_ref(v___y_1842_);
lean_inc(v_a_1806_);
lean_inc(v_fst_1835_);
lean_inc(v_fst_1831_);
v___x_1850_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1831_, v_fst_1835_, v_a_1806_, v___y_1842_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
lean_inc_ref(v___y_1842_);
lean_inc(v_a_1806_);
lean_inc_ref(v_docCtx_1790_);
v___x_1852_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1790_, v_a_1806_, v_a_1851_, v___y_1842_, v___y_1841_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v_a_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1852_, 1);
lean_inc(v_a_1806_);
v___x_1853_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1790_, v_a_1806_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref_known(v___x_1853_, 1);
v___x_1854_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1836_, v___y_1841_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1821_, v___x_1802_, v_a_1806_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v_declName_1858_; lean_object* v___x_1859_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_n(v_a_1857_, 2);
lean_dec_ref_known(v___x_1856_, 1);
v_declName_1858_ = lean_ctor_get(v___y_1842_, 3);
lean_inc_n(v_declName_1858_, 2);
lean_dec_ref(v___y_1842_);
v___x_1859_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1857_, v_declName_1858_, v_fst_1831_, v_fst_1835_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_declName_1860_; lean_object* v_type_1861_; lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1859_, 1);
v_declName_1860_ = lean_ctor_get(v_a_1855_, 3);
v_type_1861_ = lean_ctor_get(v_a_1855_, 6);
lean_inc(v_declName_1860_);
v___x_1862_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1860_, v___y_1849_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref_known(v___x_1862_, 1);
lean_inc_ref(v_type_1861_);
v___x_1863_ = l_Lean_Meta_isProp(v_type_1861_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; uint8_t v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = lean_unbox(v_a_1864_);
lean_dec(v_a_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_inc(v_declName_1858_);
v___x_1866_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1855_, v_declName_1858_, v___y_1843_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_dec_ref_known(v___x_1866_, 1);
v___y_1809_ = v_a_1857_;
v___y_1810_ = v_declName_1858_;
v___y_1811_ = v___y_1844_;
v___y_1812_ = v___y_1845_;
v___y_1813_ = v___y_1846_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1848_;
v___y_1816_ = v___y_1849_;
goto v___jp_1808_;
}
else
{
lean_dec(v_declName_1858_);
lean_dec(v_a_1857_);
return v___x_1866_;
}
}
else
{
lean_dec(v_a_1855_);
lean_dec_ref(v___y_1843_);
v___y_1809_ = v_a_1857_;
v___y_1810_ = v_declName_1858_;
v___y_1811_ = v___y_1844_;
v___y_1812_ = v___y_1845_;
v___y_1813_ = v___y_1846_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1848_;
v___y_1816_ = v___y_1849_;
goto v___jp_1808_;
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_declName_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1855_);
lean_dec_ref(v___y_1843_);
v_a_1867_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1863_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1863_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_dec(v_declName_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1855_);
lean_dec_ref(v___y_1843_);
return v___x_1862_;
}
}
else
{
lean_dec(v_declName_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1855_);
lean_dec_ref(v___y_1843_);
return v___x_1859_;
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1855_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1856_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1856_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
v_a_1883_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1854_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1854_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
return v___x_1853_;
}
}
else
{
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec_ref(v_docCtx_1790_);
return v___x_1852_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec_ref(v_docCtx_1790_);
v_a_1891_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1850_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1850_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
v___jp_1901_:
{
lean_object* v_declName_1911_; lean_object* v_type_1912_; lean_object* v_numFixed_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v_declName_1911_ = lean_ctor_get(v_snd_1836_, 3);
v_type_1912_ = lean_ctor_get(v_snd_1836_, 6);
v_numFixed_1913_ = lean_ctor_get(v_fst_1831_, 0);
v___x_1914_ = lean_box_usize(v_sz_1821_);
v___x_1915_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1831_);
lean_inc(v_declName_1911_);
lean_inc(v_fst_1835_);
lean_inc(v_snd_1836_);
lean_inc(v_a_1806_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1916_, 0, v___x_1914_);
lean_closure_set(v___f_1916_, 1, v___x_1915_);
lean_closure_set(v___f_1916_, 2, v_a_1806_);
lean_closure_set(v___f_1916_, 3, v_snd_1836_);
lean_closure_set(v___f_1916_, 4, v___y_1902_);
lean_closure_set(v___f_1916_, 5, v_fst_1835_);
lean_closure_set(v___f_1916_, 6, v___x_1807_);
lean_closure_set(v___f_1916_, 7, v___x_1900_);
lean_closure_set(v___f_1916_, 8, v_declName_1911_);
lean_closure_set(v___f_1916_, 9, v_fst_1831_);
lean_closure_set(v___f_1916_, 10, v_wf_1904_);
lean_inc(v_numFixed_1913_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_numFixed_1913_);
v___x_1918_ = 0;
lean_inc_ref(v_type_1912_);
v___x_1919_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1912_, v___x_1917_, v___f_1916_, v___x_1918_, v___x_1918_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; uint8_t v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1900_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = lean_unbox(v_a_1922_);
lean_dec(v_a_1922_);
if (v___x_1923_ == 0)
{
lean_del_object(v___x_1838_);
lean_del_object(v___x_1833_);
v___y_1841_ = v___x_1918_;
v___y_1842_ = v_a_1920_;
v___y_1843_ = v___y_1903_;
v___y_1844_ = v___y_1905_;
v___y_1845_ = v___y_1906_;
v___y_1846_ = v___y_1907_;
v___y_1847_ = v___y_1908_;
v___y_1848_ = v___y_1909_;
v___y_1849_ = v___y_1910_;
goto v___jp_1840_;
}
else
{
lean_object* v_declName_1924_; lean_object* v_value_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v_declName_1924_ = lean_ctor_get(v_a_1920_, 3);
v_value_1925_ = lean_ctor_get(v_a_1920_, 7);
v___x_1926_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1924_);
v___x_1927_ = l_Lean_MessageData_ofName(v_declName_1924_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 7);
lean_ctor_set(v___x_1838_, 1, v___x_1927_);
lean_ctor_set(v___x_1838_, 0, v___x_1926_);
v___x_1929_ = v___x_1838_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 7);
lean_ctor_set(v___x_1833_, 1, v___x_1930_);
lean_ctor_set(v___x_1833_, 0, v___x_1929_);
v___x_1932_ = v___x_1833_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_inc_ref(v_value_1925_);
v___x_1933_ = l_Lean_MessageData_ofExpr(v_value_1925_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1900_, v___x_1934_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1841_ = v___x_1918_;
v___y_1842_ = v_a_1920_;
v___y_1843_ = v___y_1903_;
v___y_1844_ = v___y_1905_;
v___y_1845_ = v___y_1906_;
v___y_1846_ = v___y_1907_;
v___y_1847_ = v___y_1908_;
v___y_1848_ = v___y_1909_;
v___y_1849_ = v___y_1910_;
goto v___jp_1840_;
}
else
{
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1903_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec_ref(v_docCtx_1790_);
return v___x_1935_;
}
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v___y_1903_);
lean_del_object(v___x_1838_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec_ref(v_docCtx_1790_);
v_a_1938_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1919_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1919_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1946_:
{
if (lean_obj_tag(v_termMeasures_x3f_1803_) == 1)
{
lean_object* v_val_1956_; 
lean_dec_ref(v___y_1949_);
v_val_1956_ = lean_ctor_get(v_termMeasures_x3f_1803_, 0);
lean_inc(v_val_1956_);
lean_dec_ref_known(v_termMeasures_x3f_1803_, 1);
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v_wf_1904_ = v_val_1956_;
v___y_1905_ = v___y_1950_;
v___y_1906_ = v___y_1951_;
v___y_1907_ = v___y_1952_;
v___y_1908_ = v___y_1953_;
v___y_1909_ = v___y_1954_;
v___y_1910_ = v___y_1955_;
goto v___jp_1901_;
}
else
{
uint8_t v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_termMeasures_x3f_1803_);
v___x_1957_ = 1;
v___x_1958_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1949_, v___x_1957_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v_wf_1904_ = v_a_1959_;
v___y_1905_ = v___y_1950_;
v___y_1906_ = v___y_1951_;
v___y_1907_ = v___y_1952_;
v___y_1908_ = v___y_1953_;
v___y_1909_ = v___y_1954_;
v___y_1910_ = v___y_1955_;
goto v___jp_1901_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_del_object(v___x_1838_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec_ref(v_docCtx_1790_);
v_a_1960_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
v___jp_1968_:
{
lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = lean_st_ref_get(v___y_1974_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref(v_env_1976_);
lean_dec(v___x_1975_);
v___x_1977_ = l_Lean_Environment_unlockAsync(v_env_1976_);
v___x_1978_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1977_, v___f_1899_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1997_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_fst_1980_ = lean_ctor_get(v_a_1979_, 0);
v_snd_1981_ = lean_ctor_get(v_a_1979_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1983_ = v_a_1979_;
v_isShared_1984_ = v_isSharedCheck_1997_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_snd_1981_);
lean_inc(v_fst_1980_);
lean_dec(v_a_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1997_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; uint8_t v___x_1988_; 
lean_inc(v_fst_1835_);
lean_inc(v_fst_1831_);
lean_inc(v_fst_1980_);
lean_inc(v_a_1806_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1985_, 0, v_a_1806_);
lean_closure_set(v___f_1985_, 1, v_fst_1980_);
lean_closure_set(v___f_1985_, 2, v_fst_1831_);
lean_closure_set(v___f_1985_, 3, v_fst_1835_);
v___x_1986_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1900_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v___x_1988_ = lean_unbox(v_a_1987_);
lean_dec(v_a_1987_);
if (v___x_1988_ == 0)
{
lean_del_object(v___x_1983_);
v___y_1947_ = v_fst_1980_;
v___y_1948_ = v_snd_1981_;
v___y_1949_ = v___f_1985_;
v___y_1950_ = v___y_1969_;
v___y_1951_ = v___y_1970_;
v___y_1952_ = v___y_1971_;
v___y_1953_ = v___y_1972_;
v___y_1954_ = v___y_1973_;
v___y_1955_ = v___y_1974_;
goto v___jp_1946_;
}
else
{
lean_object* v_value_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v_value_1989_ = lean_ctor_get(v_snd_1836_, 7);
v___x_1990_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_1989_);
v___x_1991_ = l_Lean_MessageData_ofExpr(v_value_1989_);
v___x_1992_ = l_Lean_indentD(v___x_1991_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 7);
lean_ctor_set(v___x_1983_, 1, v___x_1992_);
lean_ctor_set(v___x_1983_, 0, v___x_1990_);
v___x_1994_ = v___x_1983_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1900_, v___x_1994_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref_known(v___x_1995_, 1);
v___y_1947_ = v_fst_1980_;
v___y_1948_ = v_snd_1981_;
v___y_1949_ = v___f_1985_;
v___y_1950_ = v___y_1969_;
v___y_1951_ = v___y_1970_;
v___y_1952_ = v___y_1971_;
v___y_1953_ = v___y_1972_;
v___y_1954_ = v___y_1973_;
v___y_1955_ = v___y_1974_;
goto v___jp_1946_;
}
else
{
lean_dec_ref(v___f_1985_);
lean_dec(v_snd_1981_);
lean_dec(v_fst_1980_);
lean_del_object(v___x_1838_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec(v_termMeasures_x3f_1803_);
lean_dec_ref(v_docCtx_1790_);
return v___x_1995_;
}
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_del_object(v___x_1838_);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_fst_1831_);
lean_dec(v_a_1806_);
lean_dec(v_termMeasures_x3f_1803_);
lean_dec_ref(v_docCtx_1790_);
v_a_1998_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1978_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1978_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_a_1806_);
lean_dec(v_termMeasures_x3f_1803_);
lean_dec_ref(v_docCtx_1790_);
v_a_2017_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1828_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1828_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
v___jp_1808_:
{
size_t v_sz_1817_; lean_object* v___x_1818_; 
v_sz_1817_ = lean_array_size(v___y_1809_);
lean_inc(v___y_1810_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1810_, v___y_1809_, v_sz_1817_, v___x_1802_, v___x_1807_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
lean_dec_ref_known(v___x_1818_, 1);
v___x_1819_ = l_Lean_enableRealizationsForConst(v___y_1810_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; 
lean_dec_ref_known(v___x_1819_, 1);
v___x_1820_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1809_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1820_;
}
else
{
lean_dec_ref(v___y_1809_);
return v___x_1819_;
}
}
else
{
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_termMeasures_x3f_1803_);
lean_dec_ref(v_docCtx_1790_);
v_a_2025_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1805_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1805_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2033_, lean_object* v_preDefs_2034_, lean_object* v_termMeasure_x3fs_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Elab_wfRecursion(v_docCtx_2033_, v_preDefs_2034_, v_termMeasure_x3fs_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2044_, lean_object* v_msg_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2054_, lean_object* v_msg_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2054_, v_msg_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t v_sz_2064_, size_t v_i_2065_, lean_object* v_bs_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_2064_, v_i_2065_, v_bs_2066_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
size_t v_sz_boxed_2085_; size_t v_i_boxed_2086_; lean_object* v_res_2087_; 
v_sz_boxed_2085_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2086_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_boxed_2085_, v_i_boxed_2086_, v_bs_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_as_2088_, size_t v_sz_2089_, size_t v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_2088_, v_sz_2089_, v_i_2090_, v_b_2091_, v___y_2096_, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_as_2100_, lean_object* v_sz_2101_, lean_object* v_i_2102_, lean_object* v_b_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
size_t v_sz_boxed_2111_; size_t v_i_boxed_2112_; lean_object* v_res_2113_; 
v_sz_boxed_2111_ = lean_unbox_usize(v_sz_2101_);
lean_dec(v_sz_2101_);
v_i_boxed_2112_ = lean_unbox_usize(v_i_2102_);
lean_dec(v_i_2102_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2100_, v_sz_boxed_2111_, v_i_boxed_2112_, v_b_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_as_2100_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_a_2114_, lean_object* v_as_2115_, size_t v_sz_2116_, size_t v_i_2117_, lean_object* v_bs_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_2114_, v_sz_2116_, v_i_2117_, v_bs_2118_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_a_2127_, lean_object* v_as_2128_, lean_object* v_sz_2129_, lean_object* v_i_2130_, lean_object* v_bs_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
size_t v_sz_boxed_2139_; size_t v_i_boxed_2140_; lean_object* v_res_2141_; 
v_sz_boxed_2139_ = lean_unbox_usize(v_sz_2129_);
lean_dec(v_sz_2129_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2127_, v_as_2128_, v_sz_boxed_2139_, v_i_boxed_2140_, v_bs_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec_ref(v_as_2128_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_a_2142_, lean_object* v___x_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_bs_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_2142_, v___x_2143_, v_sz_2144_, v_i_2145_, v_bs_2146_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_a_2155_, lean_object* v___x_2156_, lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_bs_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2155_, v___x_2156_, v_sz_boxed_2167_, v_i_boxed_2168_, v_bs_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_00_u03b1_2170_, lean_object* v_env_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_2171_, v_x_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_env_2182_, lean_object* v_x_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(v_00_u03b1_2181_, v_env_2182_, v_x_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2192_, lean_object* v_msg_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2192_, v_msg_2193_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2202_, v_msg_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_bs_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2212_, v_i_2213_, v_bs_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2223_, lean_object* v_i_2224_, lean_object* v_bs_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
size_t v_sz_boxed_2233_; size_t v_i_boxed_2234_; lean_object* v_res_2235_; 
v_sz_boxed_2233_ = lean_unbox_usize(v_sz_2223_);
lean_dec(v_sz_2223_);
v_i_boxed_2234_ = lean_unbox_usize(v_i_2224_);
lean_dec(v_i_2224_);
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2233_, v_i_boxed_2234_, v_bs_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2236_, lean_object* v_as_2237_, size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2236_, v_as_2237_, v_sz_2238_, v_i_2239_, v_b_2240_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2249_, lean_object* v_as_2250_, lean_object* v_sz_2251_, lean_object* v_i_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2251_);
lean_dec(v_sz_2251_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2249_, v_as_2250_, v_sz_boxed_2261_, v_i_boxed_2262_, v_b_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_as_2250_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2264_, lean_object* v_x_2265_, uint8_t v_isExporting_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2265_, v_isExporting_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_x_2276_, lean_object* v_isExporting_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v_isExporting_boxed_2285_; lean_object* v_res_2286_; 
v_isExporting_boxed_2285_ = lean_unbox(v_isExporting_2277_);
v_res_2286_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2275_, v_x_2276_, v_isExporting_boxed_2285_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2287_, lean_object* v_x_2288_, uint8_t v_when_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2288_, v_when_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2298_, lean_object* v_x_2299_, lean_object* v_when_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
uint8_t v_when_boxed_2308_; lean_object* v_res_2309_; 
v_when_boxed_2308_ = lean_unbox(v_when_2300_);
v_res_2309_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2298_, v_x_2299_, v_when_boxed_2308_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2310_, lean_object* v_macroStack_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2310_, v_macroStack_2311_, v___y_2316_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2320_, lean_object* v_macroStack_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2320_, v_macroStack_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2330_, lean_object* v_msgData_2331_, uint8_t v_severity_2332_, uint8_t v_isSilent_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2330_, v_msgData_2331_, v_severity_2332_, v_isSilent_2333_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2342_, lean_object* v_msgData_2343_, lean_object* v_severity_2344_, lean_object* v_isSilent_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_severity_boxed_2353_; uint8_t v_isSilent_boxed_2354_; lean_object* v_res_2355_; 
v_severity_boxed_2353_ = lean_unbox(v_severity_2344_);
v_isSilent_boxed_2354_ = lean_unbox(v_isSilent_2345_);
v_res_2355_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2342_, v_msgData_2343_, v_severity_boxed_2353_, v_isSilent_boxed_2354_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_ref_2342_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2427_ = 0;
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2429_ = l_Lean_registerTraceClass(v___x_2426_, v___x_2427_, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2431_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
}
#ifdef __cplusplus
}
#endif
