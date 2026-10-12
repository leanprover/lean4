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
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object* v_env_8_, lean_object* v___y_9_, lean_object* v___y_10_){
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
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_8_ = stack[0].m_obj;
lean_object* v___y_9_ = stack[1].m_obj;
lean_object* v___y_10_ = stack[2].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_8_, v___y_9_, v___y_10_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec(v___y_51_);
return v_res_54_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_55_, v___y_59_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_55_ = stack[0].m_obj;
lean_object* v___y_56_ = stack[1].m_obj;
lean_object* v___y_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v___y_59_ = stack[4].m_obj;
lean_object* v___y_60_ = stack[5].m_obj;
lean_object* v___y_61_ = stack[6].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_73_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v_b_77_, lean_object* v_c_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
v___x_84_ = lean_apply_9(v_k_74_, v_b_77_, v_c_78_, v___y_75_, v___y_76_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_74_ = stack[0].m_obj;
lean_object* v___y_75_ = stack[1].m_obj;
lean_object* v___y_76_ = stack[2].m_obj;
lean_object* v_b_77_ = stack[3].m_obj;
lean_object* v_c_78_ = stack[4].m_obj;
lean_object* v___y_79_ = stack[5].m_obj;
lean_object* v___y_80_ = stack[6].m_obj;
lean_object* v___y_81_ = stack[7].m_obj;
lean_object* v___y_82_ = stack[8].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_74_, v___y_75_, v___y_76_, v_b_77_, v_c_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v_b_89_, lean_object* v_c_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_86_, v___y_87_, v___y_88_, v_b_89_, v_c_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_96_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_97_, lean_object* v_maxFVars_x3f_98_, lean_object* v_k_99_, uint8_t v_cleanupAnnotations_100_, uint8_t v_whnfType_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___f_109_; lean_object* v___x_110_; 
lean_inc(v___y_103_);
lean_inc_ref(v___y_102_);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_109_, 0, v_k_99_);
lean_closure_set(v___f_109_, 1, v___y_102_);
lean_closure_set(v___f_109_, 2, v___y_103_);
v___x_110_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_97_, v_maxFVars_x3f_98_, v___f_109_, v_cleanupAnnotations_100_, v_whnfType_101_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_110_) == 0)
{
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_97_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_98_ = stack[1].m_obj;
lean_object* v_k_99_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_100_ = stack[3].m_num;
uint8_t v_whnfType_101_ = stack[4].m_num;
lean_object* v___y_102_ = stack[5].m_obj;
lean_object* v___y_103_ = stack[6].m_obj;
lean_object* v___y_104_ = stack[7].m_obj;
lean_object* v___y_105_ = stack[8].m_obj;
lean_object* v___y_106_ = stack[9].m_obj;
lean_object* v___y_107_ = stack[10].m_obj;
lean_object* v_res_119_;
v_res_119_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_97_, v_maxFVars_x3f_98_, v_k_99_, v_cleanupAnnotations_100_, v_whnfType_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_120_, lean_object* v_maxFVars_x3f_121_, lean_object* v_k_122_, lean_object* v_cleanupAnnotations_123_, lean_object* v_whnfType_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_132_; uint8_t v_whnfType_boxed_133_; lean_object* v_res_134_; 
v_cleanupAnnotations_boxed_132_ = lean_unbox(v_cleanupAnnotations_123_);
v_whnfType_boxed_133_ = lean_unbox(v_whnfType_124_);
v_res_134_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_120_, v_maxFVars_x3f_121_, v_k_122_, v_cleanupAnnotations_boxed_132_, v_whnfType_boxed_133_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_134_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_135_, lean_object* v_type_136_, lean_object* v_maxFVars_x3f_137_, lean_object* v_k_138_, uint8_t v_cleanupAnnotations_139_, uint8_t v_whnfType_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_136_, v_maxFVars_x3f_137_, v_k_138_, v_cleanupAnnotations_139_, v_whnfType_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_136_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_137_ = stack[2].m_obj;
lean_object* v_k_138_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_139_ = stack[4].m_num;
uint8_t v_whnfType_140_ = stack[5].m_num;
lean_object* v___y_141_ = stack[6].m_obj;
lean_object* v___y_142_ = stack[7].m_obj;
lean_object* v___y_143_ = stack[8].m_obj;
lean_object* v___y_144_ = stack[9].m_obj;
lean_object* v___y_145_ = stack[10].m_obj;
lean_object* v___y_146_ = stack[11].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_box(0), v_type_136_, v_maxFVars_x3f_137_, v_k_138_, v_cleanupAnnotations_139_, v_whnfType_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_150_, lean_object* v_type_151_, lean_object* v_maxFVars_x3f_152_, lean_object* v_k_153_, lean_object* v_cleanupAnnotations_154_, lean_object* v_whnfType_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_163_; uint8_t v_whnfType_boxed_164_; lean_object* v_res_165_; 
v_cleanupAnnotations_boxed_163_ = lean_unbox(v_cleanupAnnotations_154_);
v_whnfType_boxed_164_ = lean_unbox(v_whnfType_155_);
v_res_165_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_150_, v_type_151_, v_maxFVars_x3f_152_, v_k_153_, v_cleanupAnnotations_boxed_163_, v_whnfType_boxed_164_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_165_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_as_166_, size_t v_sz_167_, size_t v_i_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_lt(v_i_168_, v_sz_167_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v_b_169_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_177_; 
v___x_175_ = lean_box(0);
v_a_176_ = lean_array_uget_borrowed(v_as_166_, v_i_168_);
v___x_177_ = l_Lean_Elab_addAsAxiom___redArg(v_a_176_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_177_) == 0)
{
size_t v___x_178_; size_t v___x_179_; 
lean_dec_ref_known(v___x_177_, 1);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_168_, v___x_178_);
v_i_168_ = v___x_179_;
v_b_169_ = v___x_175_;
goto _start;
}
else
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_166_ = stack[0].m_obj;
size_t v_sz_167_ = stack[1].m_num;
size_t v_i_168_ = stack[2].m_num;
lean_object* v_b_169_ = stack[3].m_obj;
lean_object* v___y_170_ = stack[4].m_obj;
lean_object* v___y_171_ = stack[5].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_166_, v_sz_167_, v_i_168_, v_b_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_as_182_, lean_object* v_sz_183_, lean_object* v_i_184_, lean_object* v_b_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
size_t v_sz_boxed_189_; size_t v_i_boxed_190_; lean_object* v_res_191_; 
v_sz_boxed_189_ = lean_unbox_usize(v_sz_183_);
lean_dec(v_sz_183_);
v_i_boxed_190_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_182_, v_sz_boxed_189_, v_i_boxed_190_, v_b_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec_ref(v_as_182_);
return v_res_191_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object* v_a_192_, size_t v_sz_193_, size_t v_i_194_, lean_object* v_bs_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = lean_usize_dec_lt(v_i_194_, v_sz_193_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec_ref(v_a_192_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_bs_195_);
return v___x_202_;
}
else
{
lean_object* v_v_203_; lean_object* v___x_204_; lean_object* v_bs_x27_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_v_203_ = lean_array_uget(v_bs_195_, v_i_194_);
v___x_204_ = lean_unsigned_to_nat(0u);
v_bs_x27_205_ = lean_array_uset(v_bs_195_, v_i_194_, v___x_204_);
v___x_206_ = lean_usize_to_nat(v_i_194_);
lean_inc_ref(v_a_192_);
v___x_207_ = l_Lean_Elab_WF_varyingVarNames(v_a_192_, v___x_206_, v_v_203_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_194_, v___x_209_);
v___x_211_ = lean_array_uset(v_bs_x27_205_, v_i_194_, v_a_208_);
v_i_194_ = v___x_210_;
v_bs_195_ = v___x_211_;
goto _start;
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_bs_x27_205_);
lean_dec_ref(v_a_192_);
v_a_213_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_207_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_207_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_192_ = stack[0].m_obj;
size_t v_sz_193_ = stack[1].m_num;
size_t v_i_194_ = stack[2].m_num;
lean_object* v_bs_195_ = stack[3].m_obj;
lean_object* v___y_196_ = stack[4].m_obj;
lean_object* v___y_197_ = stack[5].m_obj;
lean_object* v___y_198_ = stack[6].m_obj;
lean_object* v___y_199_ = stack[7].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_192_, v_sz_193_, v_i_194_, v_bs_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object* v_a_222_, lean_object* v_sz_223_, lean_object* v_i_224_, lean_object* v_bs_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
size_t v_sz_boxed_231_; size_t v_i_boxed_232_; lean_object* v_res_233_; 
v_sz_boxed_231_ = lean_unbox_usize(v_sz_223_);
lean_dec(v_sz_223_);
v_i_boxed_232_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_222_, v_sz_boxed_231_, v_i_boxed_232_, v_bs_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_233_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(1);
v___x_235_ = l_Lean_MessageData_ofFormat(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_240_ = l_Lean_MessageData_ofFormat(v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
return v_x_241_;
}
else
{
lean_object* v_head_243_; lean_object* v_tail_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_266_; 
v_head_243_ = lean_ctor_get(v_x_242_, 0);
v_tail_244_ = lean_ctor_get(v_x_242_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_266_ == 0)
{
v___x_246_ = v_x_242_;
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_tail_244_);
lean_inc(v_head_243_);
lean_dec(v_x_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_before_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_264_; 
v_before_248_ = lean_ctor_get(v_head_243_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_head_243_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_head_243_, 1);
lean_dec(v_unused_265_);
v___x_250_ = v_head_243_;
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_before_248_);
lean_dec(v_head_243_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_264_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 7);
lean_ctor_set(v___x_250_, 1, v___x_252_);
lean_ctor_set(v___x_250_, 0, v_x_241_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_x_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_263_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 7);
lean_ctor_set(v___x_246_, 1, v___x_255_);
lean_ctor_set(v___x_246_, 0, v___x_254_);
v___x_257_ = v___x_246_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_255_);
v___x_257_ = v_reuseFailAlloc_262_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = l_Lean_MessageData_ofSyntax(v_before_248_);
v___x_259_ = l_Lean_indentD(v___x_258_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_257_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v_x_241_ = v___x_260_;
v_x_242_ = v_tail_244_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_267_, lean_object* v_opt_268_){
_start:
{
lean_object* v_name_269_; lean_object* v_defValue_270_; lean_object* v_map_271_; lean_object* v___x_272_; 
v_name_269_ = lean_ctor_get(v_opt_268_, 0);
v_defValue_270_ = lean_ctor_get(v_opt_268_, 1);
v_map_271_ = lean_ctor_get(v_opts_267_, 0);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_271_, v_name_269_);
if (lean_obj_tag(v___x_272_) == 0)
{
uint8_t v___x_273_; 
v___x_273_ = lean_unbox(v_defValue_270_);
return v___x_273_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_272_, 1);
if (lean_obj_tag(v_val_274_) == 1)
{
uint8_t v_v_275_; 
v_v_275_ = lean_ctor_get_uint8(v_val_274_, 0);
lean_dec_ref_known(v_val_274_, 0);
return v_v_275_;
}
else
{
uint8_t v___x_276_; 
lean_dec(v_val_274_);
v___x_276_ = lean_unbox(v_defValue_270_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_267_ = stack[0].m_obj;
lean_object* v_opt_268_ = stack[1].m_obj;
uint8_t v_res_277_;
v_res_277_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_267_, v_opt_268_);
stack->m_num = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_278_, lean_object* v_opt_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_278_, v_opt_279_);
lean_dec_ref(v_opt_279_);
lean_dec_ref(v_opts_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_286_ = l_Lean_MessageData_ofFormat(v___x_285_);
return v___x_286_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_287_, lean_object* v_macroStack_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_289_);
v___x_292_ = l_Lean_Elab_pp_macroStack;
v___x_293_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v___x_291_, v___x_292_);
lean_dec_ref(v___x_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_macroStack_288_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v_msgData_287_);
return v___x_294_;
}
else
{
if (lean_obj_tag(v_macroStack_288_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v_msgData_287_);
return v___x_295_;
}
else
{
lean_object* v_head_296_; lean_object* v_after_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_312_; 
v_head_296_ = lean_ctor_get(v_macroStack_288_, 0);
lean_inc(v_head_296_);
v_after_297_ = lean_ctor_get(v_head_296_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_head_296_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v_head_296_, 0);
lean_dec(v_unused_313_);
v___x_299_ = v_head_296_;
v_isShared_300_ = v_isSharedCheck_312_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_after_297_);
lean_dec(v_head_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_312_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_300_ == 0)
{
lean_ctor_set_tag(v___x_299_, 7);
lean_ctor_set(v___x_299_, 1, v___x_301_);
lean_ctor_set(v___x_299_, 0, v_msgData_287_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_msgData_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_311_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_msgData_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_304_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_MessageData_ofSyntax(v_after_297_);
v___x_307_ = l_Lean_indentD(v___x_306_);
v_msgData_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_308_, 0, v___x_305_);
lean_ctor_set(v_msgData_308_, 1, v___x_307_);
v___x_309_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_308_, v_macroStack_288_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_287_ = stack[0].m_obj;
lean_object* v_macroStack_288_ = stack[1].m_obj;
lean_object* v___y_289_ = stack[2].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_287_, v_macroStack_288_, v___y_289_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_315_, lean_object* v_macroStack_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_315_, v_macroStack_316_, v___y_317_);
lean_dec_ref(v___y_317_);
return v_res_319_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; lean_object* v_env_329_; lean_object* v___x_330_; lean_object* v_toCold_331_; lean_object* v_mctx_332_; lean_object* v_lctx_333_; lean_object* v_options_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = 0;
v_env_329_ = l_Lean_Environment_setRecordingDeps(v_env_327_, v___x_328_);
v___x_330_ = lean_st_ref_get(v___y_322_);
v_toCold_331_ = lean_ctor_get(v___y_323_, 0);
v_mctx_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_mctx_332_);
lean_dec(v___x_330_);
v_lctx_333_ = lean_ctor_get(v___y_321_, 2);
v_options_334_ = lean_ctor_get(v_toCold_331_, 2);
lean_inc_ref(v_options_334_);
lean_inc_ref(v_lctx_333_);
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_env_329_);
lean_ctor_set(v___x_335_, 1, v_mctx_332_);
lean_ctor_set(v___x_335_, 2, v_lctx_333_);
lean_ctor_set(v___x_335_, 3, v_options_334_);
v___x_336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_msgData_320_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_320_ = stack[0].m_obj;
lean_object* v___y_321_ = stack[1].m_obj;
lean_object* v___y_322_ = stack[2].m_obj;
lean_object* v___y_323_ = stack[3].m_obj;
lean_object* v___y_324_ = stack[4].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_345_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_ref_354_; lean_object* v_macroStack_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_368_; 
v_ref_354_ = lean_ctor_get(v___y_351_, 2);
v_macroStack_355_ = lean_ctor_get(v___y_347_, 1);
v___x_356_ = l_Lean_Elab_getBetterRef(v_ref_354_, v_macroStack_355_);
v___x_357_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_346_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
lean_inc(v_macroStack_355_);
v___x_359_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_358_, v_macroStack_355_, v___y_351_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_368_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_356_);
lean_ctor_set(v___x_364_, 1, v_a_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 1);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_346_ = stack[0].m_obj;
lean_object* v___y_347_ = stack[1].m_obj;
lean_object* v___y_348_ = stack[2].m_obj;
lean_object* v___y_349_ = stack[3].m_obj;
lean_object* v___y_350_ = stack[4].m_obj;
lean_object* v___y_351_ = stack[5].m_obj;
lean_object* v___y_352_ = stack[6].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object* v_as_385_, size_t v_sz_386_, size_t v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_a_397_; uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_b_388_);
return v___x_402_;
}
else
{
lean_object* v_array_403_; lean_object* v_start_404_; lean_object* v_stop_405_; uint8_t v___x_406_; 
v_array_403_ = lean_ctor_get(v_b_388_, 0);
v_start_404_ = lean_ctor_get(v_b_388_, 1);
v_stop_405_ = lean_ctor_get(v_b_388_, 2);
v___x_406_ = lean_nat_dec_lt(v_start_404_, v_stop_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_b_388_);
return v___x_407_;
}
else
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_436_; 
lean_inc(v_stop_405_);
lean_inc(v_start_404_);
lean_inc_ref(v_array_403_);
v_isSharedCheck_436_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; lean_object* v_unused_438_; lean_object* v_unused_439_; 
v_unused_437_ = lean_ctor_get(v_b_388_, 2);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_b_388_, 1);
lean_dec(v_unused_438_);
v_unused_439_ = lean_ctor_get(v_b_388_, 0);
lean_dec(v_unused_439_);
v___x_409_ = v_b_388_;
v_isShared_410_ = v_isSharedCheck_436_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_b_388_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_436_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_a_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_a_411_ = lean_array_uget_borrowed(v_as_385_, v_i_387_);
v___x_412_ = lean_array_fget(v_array_403_, v_start_404_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_start_404_, v___x_413_);
lean_dec(v_start_404_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_414_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_array_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_stop_405_);
v___x_416_ = v_reuseFailAlloc_435_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_array_get_size(v_a_411_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_nat_dec_eq(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_dec(v___x_412_);
v_a_397_ = v___x_416_;
goto v___jp_396_;
}
else
{
lean_object* v_declName_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_declName_420_ = lean_ctor_get(v___x_412_, 3);
lean_inc(v_declName_420_);
lean_dec(v___x_412_);
v___x_421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1);
v___x_422_ = l_Lean_MessageData_ofName(v_declName_420_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_425_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_dec_ref_known(v___x_426_, 1);
v_a_397_ = v___x_416_;
goto v___jp_396_;
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v___x_416_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
}
}
v___jp_396_:
{
size_t v___x_398_; size_t v___x_399_; 
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_387_, v___x_398_);
v_i_387_ = v___x_399_;
v_b_388_ = v_a_397_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_385_ = stack[0].m_obj;
size_t v_sz_386_ = stack[1].m_num;
size_t v_i_387_ = stack[2].m_num;
lean_object* v_b_388_ = stack[3].m_obj;
lean_object* v___y_389_ = stack[4].m_obj;
lean_object* v___y_390_ = stack[5].m_obj;
lean_object* v___y_391_ = stack[6].m_obj;
lean_object* v___y_392_ = stack[7].m_obj;
lean_object* v___y_393_ = stack[8].m_obj;
lean_object* v___y_394_ = stack[9].m_obj;
lean_object* v_res_440_;
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_385_, v_sz_386_, v_i_387_, v_b_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_as_441_, lean_object* v_sz_442_, lean_object* v_i_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_442_);
lean_dec(v_sz_442_);
v_i_boxed_453_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_441_, v_sz_boxed_452_, v_i_boxed_453_, v_b_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_as_441_);
return v_res_454_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t v_sz_455_, size_t v_i_456_, lean_object* v_bs_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_456_, v_sz_455_);
if (v___x_458_ == 0)
{
return v_bs_457_;
}
else
{
lean_object* v_v_459_; lean_object* v_declName_460_; lean_object* v___x_461_; lean_object* v_bs_x27_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v_v_459_ = lean_array_uget_borrowed(v_bs_457_, v_i_456_);
v_declName_460_ = lean_ctor_get(v_v_459_, 3);
lean_inc(v_declName_460_);
v___x_461_ = lean_unsigned_to_nat(0u);
v_bs_x27_462_ = lean_array_uset(v_bs_457_, v_i_456_, v___x_461_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_456_, v___x_463_);
v___x_465_ = lean_array_uset(v_bs_x27_462_, v_i_456_, v_declName_460_);
v_i_456_ = v___x_464_;
v_bs_457_ = v___x_465_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_455_ = stack[0].m_num;
size_t v_i_456_ = stack[1].m_num;
lean_object* v_bs_457_ = stack[2].m_obj;
lean_object* v_res_467_;
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_455_, v_i_456_, v_bs_457_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_bs_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_boxed_471_, v_i_boxed_472_, v_bs_470_);
return v_res_473_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_a_474_, lean_object* v___x_475_, size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec(v___x_475_);
lean_dec_ref(v_a_474_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_bs_478_);
return v___x_483_;
}
else
{
lean_object* v_v_484_; lean_object* v_ref_485_; uint8_t v_kind_486_; lean_object* v_levelParams_487_; lean_object* v_modifiers_488_; lean_object* v_declName_489_; lean_object* v_binders_490_; lean_object* v_numSectionVars_491_; lean_object* v_type_492_; lean_object* v_value_493_; lean_object* v_termination_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_520_; 
v_v_484_ = lean_array_uget(v_bs_478_, v_i_477_);
v_ref_485_ = lean_ctor_get(v_v_484_, 0);
v_kind_486_ = lean_ctor_get_uint8(v_v_484_, sizeof(void*)*9);
v_levelParams_487_ = lean_ctor_get(v_v_484_, 1);
v_modifiers_488_ = lean_ctor_get(v_v_484_, 2);
v_declName_489_ = lean_ctor_get(v_v_484_, 3);
v_binders_490_ = lean_ctor_get(v_v_484_, 4);
v_numSectionVars_491_ = lean_ctor_get(v_v_484_, 5);
v_type_492_ = lean_ctor_get(v_v_484_, 6);
v_value_493_ = lean_ctor_get(v_v_484_, 7);
v_termination_494_ = lean_ctor_get(v_v_484_, 8);
v_isSharedCheck_520_ = !lean_is_exclusive(v_v_484_);
if (v_isSharedCheck_520_ == 0)
{
v___x_496_ = v_v_484_;
v_isShared_497_ = v_isSharedCheck_520_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_termination_494_);
lean_inc(v_value_493_);
lean_inc(v_type_492_);
lean_inc(v_numSectionVars_491_);
lean_inc(v_binders_490_);
lean_inc(v_declName_489_);
lean_inc(v_modifiers_488_);
lean_inc(v_levelParams_487_);
lean_inc(v_ref_485_);
lean_dec(v_v_484_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_520_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
size_t v_sz_498_; lean_object* v___x_499_; lean_object* v_bs_x27_500_; size_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_sz_498_ = lean_array_size(v_a_474_);
v___x_499_ = lean_unsigned_to_nat(0u);
v_bs_x27_500_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_499_);
v___x_501_ = ((size_t)0ULL);
lean_inc_ref(v_a_474_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_498_, v___x_501_, v_a_474_);
lean_inc(v___x_475_);
v___x_503_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_502_, v___x_475_, v_value_493_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 7, v_a_504_);
v___x_506_ = v___x_496_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_ref_485_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_levelParams_487_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_modifiers_488_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_declName_489_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_binders_490_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_numSectionVars_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_type_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_a_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v_termination_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*9, v_kind_486_);
v___x_506_ = v_reuseFailAlloc_511_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_477_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_500_, v_i_477_, v___x_506_);
v_i_477_ = v___x_508_;
v_bs_478_ = v___x_509_;
goto _start;
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_bs_x27_500_);
lean_del_object(v___x_496_);
lean_dec_ref(v_termination_494_);
lean_dec_ref(v_type_492_);
lean_dec(v_numSectionVars_491_);
lean_dec(v_binders_490_);
lean_dec(v_declName_489_);
lean_dec_ref(v_modifiers_488_);
lean_dec(v_levelParams_487_);
lean_dec(v_ref_485_);
lean_dec(v___x_475_);
lean_dec_ref(v_a_474_);
v_a_512_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_503_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_474_ = stack[0].m_obj;
lean_object* v___x_475_ = stack[1].m_obj;
size_t v_sz_476_ = stack[2].m_num;
size_t v_i_477_ = stack[3].m_num;
lean_object* v_bs_478_ = stack[4].m_obj;
lean_object* v___y_479_ = stack[5].m_obj;
lean_object* v___y_480_ = stack[6].m_obj;
lean_object* v_res_521_;
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_474_, v___x_475_, v_sz_476_, v_i_477_, v_bs_478_, v___y_479_, v___y_480_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_a_522_, lean_object* v___x_523_, lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_bs_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_sz_boxed_530_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_531_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_522_, v___x_523_, v_sz_boxed_530_, v_i_boxed_531_, v_bs_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_533_, size_t v_sz_534_, size_t v___x_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_533_, v_sz_534_, v___x_535_, v___x_536_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
lean_dec_ref_known(v___x_545_, 1);
lean_inc_ref(v_a_533_);
v___x_546_ = l_Lean_Elab_getFixedParamPerms(v_a_533_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_n(v_a_547_, 2);
lean_dec_ref_known(v___x_546_, 1);
lean_inc_ref(v_a_533_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_547_, v_sz_534_, v___x_535_, v_a_533_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; size_t v_sz_553_; lean_object* v___x_554_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_array_get_size(v_a_533_);
lean_inc_ref(v_a_533_);
v___x_552_ = l_Array_toSubarray___redArg(v_a_533_, v___x_550_, v___x_551_);
v_sz_553_ = lean_array_size(v_a_549_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_a_549_, v_sz_553_, v___x_535_, v___x_552_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; lean_object* v_numSectionVars_556_; lean_object* v___x_557_; 
lean_dec_ref_known(v___x_554_, 1);
v___x_555_ = lean_array_get_borrowed(v___x_537_, v_a_533_, v___x_550_);
v_numSectionVars_556_ = lean_ctor_get(v___x_555_, 5);
lean_inc(v_numSectionVars_556_);
lean_inc_ref(v_a_533_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_533_, v_numSectionVars_556_, v_sz_534_, v___x_535_, v_a_533_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
lean_inc(v_a_549_);
lean_inc(v_a_547_);
v___x_559_ = l_Lean_Elab_WF_packMutual(v_a_547_, v_a_549_, v_a_558_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_a_549_);
lean_ctor_set(v___x_564_, 1, v_a_560_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_547_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_549_);
lean_dec(v_a_547_);
v_a_570_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_559_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_559_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_549_);
lean_dec(v_a_547_);
v_a_578_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_557_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_557_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_549_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_533_);
v_a_586_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_554_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_554_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_547_);
lean_dec_ref(v_a_533_);
v_a_594_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_548_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_548_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_a_533_);
v_a_602_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_546_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_546_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_a_533_);
v_a_610_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_545_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_545_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_533_ = stack[0].m_obj;
size_t v_sz_534_ = stack[1].m_num;
size_t v___x_535_ = stack[2].m_num;
lean_object* v___x_536_ = stack[3].m_obj;
lean_object* v___x_537_ = stack[4].m_obj;
lean_object* v___y_538_ = stack[5].m_obj;
lean_object* v___y_539_ = stack[6].m_obj;
lean_object* v___y_540_ = stack[7].m_obj;
lean_object* v___y_541_ = stack[8].m_obj;
lean_object* v___y_542_ = stack[9].m_obj;
lean_object* v___y_543_ = stack[10].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Elab_wfRecursion___lam__0(v_a_533_, v_sz_534_, v___x_535_, v___x_536_, v___x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_619_, lean_object* v_sz_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
size_t v_sz_boxed_631_; size_t v___x_44365__boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_620_);
lean_dec(v_sz_620_);
v___x_44365__boxed_632_ = lean_unbox_usize(v___x_621_);
lean_dec(v___x_621_);
v_res_633_ = l_Lean_Elab_wfRecursion___lam__0(v_a_619_, v_sz_boxed_631_, v___x_44365__boxed_632_, v___x_622_, v___x_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v___x_623_);
return v_res_633_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_634_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_ref_643_; uint8_t v_kind_644_; lean_object* v_levelParams_645_; lean_object* v_modifiers_646_; lean_object* v_declName_647_; lean_object* v_binders_648_; lean_object* v_numSectionVars_649_; lean_object* v_type_650_; lean_object* v_value_651_; lean_object* v_termination_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref_known(v___x_642_, 1);
v_ref_643_ = lean_ctor_get(v_snd_634_, 0);
v_kind_644_ = lean_ctor_get_uint8(v_snd_634_, sizeof(void*)*9);
v_levelParams_645_ = lean_ctor_get(v_snd_634_, 1);
v_modifiers_646_ = lean_ctor_get(v_snd_634_, 2);
v_declName_647_ = lean_ctor_get(v_snd_634_, 3);
v_binders_648_ = lean_ctor_get(v_snd_634_, 4);
v_numSectionVars_649_ = lean_ctor_get(v_snd_634_, 5);
v_type_650_ = lean_ctor_get(v_snd_634_, 6);
v_value_651_ = lean_ctor_get(v_snd_634_, 7);
v_termination_652_ = lean_ctor_get(v_snd_634_, 8);
v_isSharedCheck_678_ = !lean_is_exclusive(v_snd_634_);
if (v_isSharedCheck_678_ == 0)
{
v___x_654_ = v_snd_634_;
v_isShared_655_ = v_isSharedCheck_678_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_termination_652_);
lean_inc(v_value_651_);
lean_inc(v_type_650_);
lean_inc(v_numSectionVars_649_);
lean_inc(v_binders_648_);
lean_inc(v_declName_647_);
lean_inc(v_modifiers_646_);
lean_inc(v_levelParams_645_);
lean_inc(v_ref_643_);
lean_dec(v_snd_634_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_678_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Elab_WF_preprocess(v_value_651_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_669_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_669_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_expr_661_; lean_object* v___x_663_; 
v_expr_661_ = lean_ctor_get(v_a_657_, 0);
lean_inc_ref(v_expr_661_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 7, v_expr_661_);
v___x_663_ = v___x_654_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_ref_643_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_levelParams_645_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_modifiers_646_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_declName_647_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_binders_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 5, v_numSectionVars_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 6, v_type_650_);
lean_ctor_set(v_reuseFailAlloc_668_, 7, v_expr_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 8, v_termination_652_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*9, v_kind_644_);
v___x_663_ = v_reuseFailAlloc_668_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_a_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_664_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_654_);
lean_dec_ref(v_termination_652_);
lean_dec_ref(v_type_650_);
lean_dec(v_numSectionVars_649_);
lean_dec(v_binders_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_modifiers_646_);
lean_dec(v_levelParams_645_);
lean_dec(v_ref_643_);
v_a_670_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_656_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_656_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_snd_634_);
v_a_679_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_642_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_642_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_634_ = stack[0].m_obj;
lean_object* v___y_635_ = stack[1].m_obj;
lean_object* v___y_636_ = stack[2].m_obj;
lean_object* v___y_637_ = stack[3].m_obj;
lean_object* v___y_638_ = stack[4].m_obj;
lean_object* v___y_639_ = stack[5].m_obj;
lean_object* v___y_640_ = stack[6].m_obj;
lean_object* v_res_687_;
v_res_687_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_696_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_toCold_708_; lean_object* v_options_709_; uint8_t v_hasTrace_710_; 
v_toCold_708_ = lean_ctor_get(v___y_705_, 0);
v_options_709_ = lean_ctor_get(v_toCold_708_, 2);
v_hasTrace_710_ = lean_ctor_get_uint8(v_options_709_, sizeof(void*)*1);
if (v_hasTrace_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v___x_700_);
v___x_711_ = lean_box(v_hasTrace_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v_inheritedTraceOptions_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_inheritedTraceOptions_713_ = lean_ctor_get(v_toCold_708_, 11);
v___x_714_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
v___x_715_ = l_Lean_Name_append(v___x_714_, v___x_700_);
v___x_716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_713_, v_options_709_, v___x_715_);
lean_dec(v___x_715_);
v___x_717_ = lean_box(v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_700_ = stack[0].m_obj;
lean_object* v___y_701_ = stack[1].m_obj;
lean_object* v___y_702_ = stack[2].m_obj;
lean_object* v___y_703_ = stack[3].m_obj;
lean_object* v___y_704_ = stack[4].m_obj;
lean_object* v___y_705_ = stack[5].m_obj;
lean_object* v___y_706_ = stack[6].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_Elab_wfRecursion___lam__2(v___x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v___x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_wfRecursion___lam__2(v___x_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_728_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_736_, uint8_t v___y_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 1)
{
lean_object* v_pre_739_; 
v_pre_739_ = lean_ctor_get(v_x_738_, 0);
switch(lean_obj_tag(v_pre_739_))
{
case 1:
{
lean_object* v_pre_740_; 
v_pre_740_ = lean_ctor_get(v_pre_739_, 0);
switch(lean_obj_tag(v_pre_740_))
{
case 0:
{
lean_object* v_str_741_; lean_object* v_str_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_str_741_ = lean_ctor_get(v_x_738_, 1);
v_str_742_ = lean_ctor_get(v_pre_739_, 1);
v___x_743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_744_ = lean_string_dec_eq(v_str_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_746_ = lean_string_dec_eq(v_str_742_, v___x_745_);
if (v___x_746_ == 0)
{
return v___x_746_;
}
else
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_748_ = lean_string_dec_eq(v_str_741_, v___x_747_);
if (v___x_748_ == 0)
{
return v___x_748_;
}
else
{
return v_suppressElabErrors_736_;
}
}
}
else
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_750_ = lean_string_dec_eq(v_str_741_, v___x_749_);
if (v___x_750_ == 0)
{
return v___x_750_;
}
else
{
return v_suppressElabErrors_736_;
}
}
}
case 1:
{
lean_object* v_pre_751_; 
v_pre_751_ = lean_ctor_get(v_pre_740_, 0);
if (lean_obj_tag(v_pre_751_) == 0)
{
lean_object* v_str_752_; lean_object* v_str_753_; lean_object* v_str_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_str_752_ = lean_ctor_get(v_x_738_, 1);
v_str_753_ = lean_ctor_get(v_pre_739_, 1);
v_str_754_ = lean_ctor_get(v_pre_740_, 1);
v___x_755_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_756_ = lean_string_dec_eq(v_str_754_, v___x_755_);
if (v___x_756_ == 0)
{
return v___x_756_;
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_758_ = lean_string_dec_eq(v_str_753_, v___x_757_);
if (v___x_758_ == 0)
{
return v___x_758_;
}
else
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_760_ = lean_string_dec_eq(v_str_752_, v___x_759_);
if (v___x_760_ == 0)
{
return v___x_760_;
}
else
{
return v_suppressElabErrors_736_;
}
}
}
}
else
{
return v___y_737_;
}
}
default: 
{
return v___y_737_;
}
}
}
case 0:
{
lean_object* v_str_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_str_761_ = lean_ctor_get(v_x_738_, 1);
v___x_762_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_763_ = lean_string_dec_eq(v_str_761_, v___x_762_);
if (v___x_763_ == 0)
{
return v___x_763_;
}
else
{
return v_suppressElabErrors_736_;
}
}
default: 
{
return v___y_737_;
}
}
}
else
{
return v___y_737_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_736_ = stack[0].m_num;
uint8_t v___y_737_ = stack[1].m_num;
lean_object* v_x_738_ = stack[2].m_obj;
uint8_t v_res_764_;
v_res_764_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_736_, v___y_737_, v_x_738_);
stack->m_num = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_765_, lean_object* v___y_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_suppressElabErrors_boxed_768_; uint8_t v___y_44864__boxed_769_; uint8_t v_res_770_; lean_object* v_r_771_; 
v_suppressElabErrors_boxed_768_ = lean_unbox(v_suppressElabErrors_765_);
v___y_44864__boxed_769_ = lean_unbox(v___y_766_);
v_res_770_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_768_, v___y_44864__boxed_769_, v_x_767_);
lean_dec(v_x_767_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_773_, lean_object* v_msgData_774_, uint8_t v_severity_775_, uint8_t v_isSilent_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v_toCold_790_; lean_object* v___y_791_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_847_; lean_object* v___y_848_; uint8_t v___y_849_; uint8_t v___y_850_; lean_object* v___y_851_; uint8_t v___y_852_; lean_object* v___y_853_; uint8_t v___y_857_; uint8_t v___y_858_; uint8_t v___y_859_; uint8_t v___x_870_; uint8_t v___y_872_; uint8_t v___y_873_; uint8_t v___y_874_; uint8_t v___y_876_; uint8_t v___x_884_; 
v___x_870_ = 2;
v___x_884_ = l_Lean_instBEqMessageSeverity_beq(v_severity_775_, v___x_870_);
if (v___x_884_ == 0)
{
v___y_876_ = v___x_884_;
goto v___jp_875_;
}
else
{
uint8_t v___x_885_; 
lean_inc_ref(v_msgData_774_);
v___x_885_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_774_);
v___y_876_ = v___x_885_;
goto v___jp_875_;
}
v___jp_782_:
{
lean_object* v_currNamespace_792_; lean_object* v_openDecls_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_env_798_; lean_object* v_nextMacroScope_799_; lean_object* v_ngen_800_; lean_object* v_auxDeclNGen_801_; lean_object* v_traceState_802_; lean_object* v_cache_803_; lean_object* v_recordedDeps_804_; lean_object* v_messages_805_; lean_object* v_infoState_806_; lean_object* v_snapshotTasks_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_818_; 
v_currNamespace_792_ = lean_ctor_get(v_toCold_790_, 4);
v_openDecls_793_ = lean_ctor_get(v_toCold_790_, 5);
lean_inc(v_openDecls_793_);
lean_inc(v_currNamespace_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_currNamespace_792_);
lean_ctor_set(v___x_794_, 1, v_openDecls_793_);
v___x_795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc_ref(v___y_788_);
v___x_796_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_796_, 0, v___y_788_);
lean_ctor_set(v___x_796_, 1, v___y_783_);
lean_ctor_set(v___x_796_, 2, v___y_786_);
lean_ctor_set(v___x_796_, 3, v___y_784_);
lean_ctor_set(v___x_796_, 4, v___x_795_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*5, v___y_787_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*5 + 1, v___y_789_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*5 + 2, v_isSilent_776_);
v___x_797_ = lean_st_ref_take(v___y_791_);
v_env_798_ = lean_ctor_get(v___x_797_, 0);
v_nextMacroScope_799_ = lean_ctor_get(v___x_797_, 1);
v_ngen_800_ = lean_ctor_get(v___x_797_, 2);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_797_, 3);
v_traceState_802_ = lean_ctor_get(v___x_797_, 4);
v_cache_803_ = lean_ctor_get(v___x_797_, 5);
v_recordedDeps_804_ = lean_ctor_get(v___x_797_, 6);
v_messages_805_ = lean_ctor_get(v___x_797_, 7);
v_infoState_806_ = lean_ctor_get(v___x_797_, 8);
v_snapshotTasks_807_ = lean_ctor_get(v___x_797_, 9);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_818_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snapshotTasks_807_);
lean_inc(v_infoState_806_);
lean_inc(v_messages_805_);
lean_inc(v_recordedDeps_804_);
lean_inc(v_cache_803_);
lean_inc(v_traceState_802_);
lean_inc(v_auxDeclNGen_801_);
lean_inc(v_ngen_800_);
lean_inc(v_nextMacroScope_799_);
lean_inc(v_env_798_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_811_ = lean_box(0);
v___x_812_ = l_Lean_MessageLog_add(v___x_796_, v_messages_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 7, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_env_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_nextMacroScope_799_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_ngen_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_auxDeclNGen_801_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_traceState_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_cache_803_);
lean_ctor_set(v_reuseFailAlloc_817_, 6, v_recordedDeps_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 7, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_817_, 8, v_infoState_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 9, v_snapshotTasks_807_);
v___x_814_ = v_reuseFailAlloc_817_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_st_ref_put(v___y_791_, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_811_);
return v___x_816_;
}
}
}
v___jp_819_:
{
lean_object* v_fileName_828_; lean_object* v_fileMap_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_845_; 
v_fileName_828_ = lean_ctor_get(v___y_822_, 0);
v_fileMap_829_ = lean_ctor_get(v___y_822_, 1);
v___x_830_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_774_);
v___x_831_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_830_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_845_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_845_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_inc_ref_n(v_fileMap_829_, 2);
v___x_836_ = l_Lean_FileMap_toPosition(v_fileMap_829_, v___y_824_);
lean_dec(v___y_824_);
v___x_837_ = l_Lean_FileMap_toPosition(v_fileMap_829_, v___y_827_);
lean_dec(v___y_827_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_823_ == 0)
{
lean_del_object(v___x_834_);
lean_dec_ref(v___y_821_);
v___y_783_ = v___x_836_;
v___y_784_ = v___x_839_;
v___y_785_ = v_a_832_;
v___y_786_ = v___x_838_;
v___y_787_ = v___y_825_;
v___y_788_ = v_fileName_828_;
v___y_789_ = v___y_826_;
v_toCold_790_ = v___y_820_;
v___y_791_ = v___y_780_;
goto v___jp_782_;
}
else
{
uint8_t v___x_840_; 
lean_inc(v_a_832_);
v___x_840_ = l_Lean_MessageData_hasTag(v___y_821_, v_a_832_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec_ref_known(v___x_838_, 1);
lean_dec_ref(v___x_836_);
lean_dec(v_a_832_);
v___x_841_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_841_);
v___x_843_ = v___x_834_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_del_object(v___x_834_);
v___y_783_ = v___x_836_;
v___y_784_ = v___x_839_;
v___y_785_ = v_a_832_;
v___y_786_ = v___x_838_;
v___y_787_ = v___y_825_;
v___y_788_ = v_fileName_828_;
v___y_789_ = v___y_826_;
v_toCold_790_ = v___y_820_;
v___y_791_ = v___y_780_;
goto v___jp_782_;
}
}
}
}
v___jp_846_:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Syntax_getTailPos_x3f(v___y_851_, v___y_850_);
lean_dec(v___y_851_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_inc(v___y_853_);
v___y_820_ = v___y_847_;
v___y_821_ = v___y_848_;
v___y_822_ = v___y_847_;
v___y_823_ = v___y_849_;
v___y_824_ = v___y_853_;
v___y_825_ = v___y_850_;
v___y_826_ = v___y_852_;
v___y_827_ = v___y_853_;
goto v___jp_819_;
}
else
{
lean_object* v_val_855_; 
v_val_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_854_, 1);
v___y_820_ = v___y_847_;
v___y_821_ = v___y_848_;
v___y_822_ = v___y_847_;
v___y_823_ = v___y_849_;
v___y_824_ = v___y_853_;
v___y_825_ = v___y_850_;
v___y_826_ = v___y_852_;
v___y_827_ = v_val_855_;
goto v___jp_819_;
}
}
v___jp_856_:
{
lean_object* v_toCold_860_; lean_object* v_ref_861_; uint8_t v_suppressElabErrors_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v_ref_866_; lean_object* v___x_867_; 
v_toCold_860_ = lean_ctor_get(v___y_779_, 0);
v_ref_861_ = lean_ctor_get(v___y_779_, 2);
v_suppressElabErrors_862_ = lean_ctor_get_uint8(v___y_779_, sizeof(void*)*3 + 2);
v___x_863_ = lean_box(v_suppressElabErrors_862_);
v___x_864_ = lean_box(v___y_857_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_865_, 0, v___x_863_);
lean_closure_set(v___f_865_, 1, v___x_864_);
v_ref_866_ = l_Lean_replaceRef(v_ref_773_, v_ref_861_);
v___x_867_ = l_Lean_Syntax_getPos_x3f(v_ref_866_, v___y_858_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_unsigned_to_nat(0u);
v___y_847_ = v_toCold_860_;
v___y_848_ = v___f_865_;
v___y_849_ = v_suppressElabErrors_862_;
v___y_850_ = v___y_858_;
v___y_851_ = v_ref_866_;
v___y_852_ = v___y_859_;
v___y_853_ = v___x_868_;
goto v___jp_846_;
}
else
{
lean_object* v_val_869_; 
v_val_869_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_867_, 1);
v___y_847_ = v_toCold_860_;
v___y_848_ = v___f_865_;
v___y_849_ = v_suppressElabErrors_862_;
v___y_850_ = v___y_858_;
v___y_851_ = v_ref_866_;
v___y_852_ = v___y_859_;
v___y_853_ = v_val_869_;
goto v___jp_846_;
}
}
v___jp_871_:
{
if (v___y_874_ == 0)
{
v___y_857_ = v___y_872_;
v___y_858_ = v___y_873_;
v___y_859_ = v_severity_775_;
goto v___jp_856_;
}
else
{
v___y_857_ = v___y_872_;
v___y_858_ = v___y_873_;
v___y_859_ = v___x_870_;
goto v___jp_856_;
}
}
v___jp_875_:
{
if (v___y_876_ == 0)
{
uint8_t v___x_877_; uint8_t v___x_878_; 
v___x_877_ = 1;
v___x_878_ = l_Lean_instBEqMessageSeverity_beq(v_severity_775_, v___x_877_);
if (v___x_878_ == 0)
{
v___y_872_ = v___y_876_;
v___y_873_ = v___y_876_;
v___y_874_ = v___x_878_;
goto v___jp_871_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_779_);
v___x_880_ = l_Lean_warningAsError;
v___x_881_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v___x_879_, v___x_880_);
lean_dec_ref(v___x_879_);
v___y_872_ = v___y_876_;
v___y_873_ = v___y_876_;
v___y_874_ = v___x_881_;
goto v___jp_871_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_msgData_774_);
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_773_ = stack[0].m_obj;
lean_object* v_msgData_774_ = stack[1].m_obj;
uint8_t v_severity_775_ = stack[2].m_num;
uint8_t v_isSilent_776_ = stack[3].m_num;
lean_object* v___y_777_ = stack[4].m_obj;
lean_object* v___y_778_ = stack[5].m_obj;
lean_object* v___y_779_ = stack[6].m_obj;
lean_object* v___y_780_ = stack[7].m_obj;
lean_object* v_res_886_;
v_res_886_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_773_, v_msgData_774_, v_severity_775_, v_isSilent_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_887_, lean_object* v_msgData_888_, lean_object* v_severity_889_, lean_object* v_isSilent_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_severity_boxed_896_; uint8_t v_isSilent_boxed_897_; lean_object* v_res_898_; 
v_severity_boxed_896_ = lean_unbox(v_severity_889_);
v_isSilent_boxed_897_ = lean_unbox(v_isSilent_890_);
v_res_898_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_887_, v_msgData_888_, v_severity_boxed_896_, v_isSilent_boxed_897_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v_ref_887_);
return v_res_898_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_899_, lean_object* v_msgData_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
v___x_908_ = 1;
v___x_909_ = 0;
v___x_910_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_899_, v_msgData_900_, v___x_908_, v___x_909_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_910_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_899_ = stack[0].m_obj;
lean_object* v_msgData_900_ = stack[1].m_obj;
lean_object* v___y_901_ = stack[2].m_obj;
lean_object* v___y_902_ = stack[3].m_obj;
lean_object* v___y_903_ = stack[4].m_obj;
lean_object* v___y_904_ = stack[5].m_obj;
lean_object* v___y_905_ = stack[6].m_obj;
lean_object* v___y_906_ = stack[7].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_899_, v_msgData_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_912_, lean_object* v_msgData_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_912_, v_msgData_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v_ref_912_);
return v_res_921_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_930_, lean_object* v_as_931_, size_t v_i_932_, size_t v_stop_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_a_943_; uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_eq(v_i_932_, v_stop_933_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v_name_949_; lean_object* v_stx_950_; uint8_t v___y_952_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_948_ = lean_array_uget_borrowed(v_as_931_, v_i_932_);
v_name_949_ = lean_ctor_get(v___x_948_, 0);
v_stx_950_ = lean_ctor_get(v___x_948_, 1);
v___x_962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_963_ = lean_name_eq(v_name_949_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_965_ = lean_name_eq(v_name_949_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
v___x_966_ = lean_box(0);
v_a_943_ = v___x_966_;
goto v___jp_942_;
}
else
{
v___y_952_ = v___x_965_;
goto v___jp_951_;
}
}
else
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_nat_dec_lt(v___x_967_, v___x_930_);
v___y_952_ = v___x_968_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_949_);
v___x_954_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_949_, v___y_952_);
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = l_Lean_MessageData_ofFormat(v___x_958_);
v___x_960_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_950_, v___x_959_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_a_943_ = v_a_961_;
goto v___jp_942_;
}
else
{
return v___x_960_;
}
}
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v_b_934_);
return v___x_969_;
}
v___jp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_932_, v___x_944_);
v_i_932_ = v___x_945_;
v_b_934_ = v_a_943_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_930_ = stack[0].m_obj;
lean_object* v_as_931_ = stack[1].m_obj;
size_t v_i_932_ = stack[2].m_num;
size_t v_stop_933_ = stack[3].m_num;
lean_object* v_b_934_ = stack[4].m_obj;
lean_object* v___y_935_ = stack[5].m_obj;
lean_object* v___y_936_ = stack[6].m_obj;
lean_object* v___y_937_ = stack[7].m_obj;
lean_object* v___y_938_ = stack[8].m_obj;
lean_object* v___y_939_ = stack[9].m_obj;
lean_object* v___y_940_ = stack[10].m_obj;
lean_object* v_res_970_;
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_930_, v_as_931_, v_i_932_, v_stop_933_, v_b_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_970_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_971_, lean_object* v_as_972_, lean_object* v_i_973_, lean_object* v_stop_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
size_t v_i_boxed_983_; size_t v_stop_boxed_984_; lean_object* v_res_985_; 
v_i_boxed_983_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_stop_boxed_984_ = lean_unbox_usize(v_stop_974_);
lean_dec(v_stop_974_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_971_, v_as_972_, v_i_boxed_983_, v_stop_boxed_984_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
lean_dec(v___x_971_);
return v_res_985_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_986_, lean_object* v_as_987_, size_t v_i_988_, size_t v_stop_989_, lean_object* v_b_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_a_999_; lean_object* v___y_1004_; uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_988_, v_stop_989_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v_modifiers_1008_; lean_object* v_attrs_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_987_, v_i_988_);
v_modifiers_1008_ = lean_ctor_get(v___x_1007_, 2);
v_attrs_1009_ = lean_ctor_get(v_modifiers_1008_, 2);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_array_get_size(v_attrs_1009_);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_nat_dec_lt(v___x_1010_, v___x_1011_);
if (v___x_1013_ == 0)
{
v_a_999_ = v___x_1012_;
goto v___jp_998_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_nat_dec_le(v___x_1011_, v___x_1011_);
if (v___x_1014_ == 0)
{
if (v___x_1013_ == 0)
{
v_a_999_ = v___x_1012_;
goto v___jp_998_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = lean_usize_of_nat(v___x_1011_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_986_, v_attrs_1009_, v___x_1015_, v___x_1016_, v___x_1012_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
v___y_1004_ = v___x_1017_;
goto v___jp_1003_;
}
}
else
{
size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = lean_usize_of_nat(v___x_1011_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_986_, v_attrs_1009_, v___x_1018_, v___x_1019_, v___x_1012_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
v___y_1004_ = v___x_1020_;
goto v___jp_1003_;
}
}
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_990_);
return v___x_1021_;
}
v___jp_998_:
{
size_t v___x_1000_; size_t v___x_1001_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_988_, v___x_1000_);
v_i_988_ = v___x_1001_;
v_b_990_ = v_a_999_;
goto _start;
}
v___jp_1003_:
{
if (lean_obj_tag(v___y_1004_) == 0)
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v___y_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___y_1004_, 1);
v_a_999_ = v_a_1005_;
goto v___jp_998_;
}
else
{
return v___y_1004_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_986_ = stack[0].m_obj;
lean_object* v_as_987_ = stack[1].m_obj;
size_t v_i_988_ = stack[2].m_num;
size_t v_stop_989_ = stack[3].m_num;
lean_object* v_b_990_ = stack[4].m_obj;
lean_object* v___y_991_ = stack[5].m_obj;
lean_object* v___y_992_ = stack[6].m_obj;
lean_object* v___y_993_ = stack[7].m_obj;
lean_object* v___y_994_ = stack[8].m_obj;
lean_object* v___y_995_ = stack[9].m_obj;
lean_object* v___y_996_ = stack[10].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_986_, v_as_987_, v_i_988_, v_stop_989_, v_b_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_1023_, lean_object* v_as_1024_, lean_object* v_i_1025_, lean_object* v_stop_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_i_boxed_1035_; size_t v_stop_boxed_1036_; lean_object* v_res_1037_; 
v_i_boxed_1035_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_stop_boxed_1036_ = lean_unbox_usize(v_stop_1026_);
lean_dec(v_stop_1026_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1023_, v_as_1024_, v_i_boxed_1035_, v_stop_boxed_1036_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
lean_dec(v___x_1023_);
return v_res_1037_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_bs_1040_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_lt(v_i_1039_, v_sz_1038_);
if (v___x_1041_ == 0)
{
return v_bs_1040_;
}
else
{
lean_object* v_v_1042_; lean_object* v_termination_1043_; lean_object* v_decreasingBy_x3f_1044_; lean_object* v___x_1045_; lean_object* v_bs_x27_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_v_1042_ = lean_array_uget_borrowed(v_bs_1040_, v_i_1039_);
v_termination_1043_ = lean_ctor_get(v_v_1042_, 8);
v_decreasingBy_x3f_1044_ = lean_ctor_get(v_termination_1043_, 4);
lean_inc(v_decreasingBy_x3f_1044_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v_bs_x27_1046_ = lean_array_uset(v_bs_1040_, v_i_1039_, v___x_1045_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1039_, v___x_1047_);
v___x_1049_ = lean_array_uset(v_bs_x27_1046_, v_i_1039_, v_decreasingBy_x3f_1044_);
v_i_1039_ = v___x_1048_;
v_bs_1040_ = v___x_1049_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1038_ = stack[0].m_num;
size_t v_i_1039_ = stack[1].m_num;
lean_object* v_bs_1040_ = stack[2].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1038_, v_i_1039_, v_bs_1040_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_bs_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
return v_res_1057_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1058_; double v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_float_of_nat(v___x_1058_);
return v___x_1059_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1062_, lean_object* v_msg_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_ref_1069_; lean_object* v___x_1070_; lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1116_; 
v_ref_1069_ = lean_ctor_get(v___y_1066_, 2);
v___x_1070_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1116_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1116_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v_traceState_1076_; lean_object* v_env_1077_; lean_object* v_nextMacroScope_1078_; lean_object* v_ngen_1079_; lean_object* v_auxDeclNGen_1080_; lean_object* v_cache_1081_; lean_object* v_recordedDeps_1082_; lean_object* v_messages_1083_; lean_object* v_infoState_1084_; lean_object* v_snapshotTasks_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1115_; 
v___x_1075_ = lean_st_ref_take(v___y_1067_);
v_traceState_1076_ = lean_ctor_get(v___x_1075_, 4);
v_env_1077_ = lean_ctor_get(v___x_1075_, 0);
v_nextMacroScope_1078_ = lean_ctor_get(v___x_1075_, 1);
v_ngen_1079_ = lean_ctor_get(v___x_1075_, 2);
v_auxDeclNGen_1080_ = lean_ctor_get(v___x_1075_, 3);
v_cache_1081_ = lean_ctor_get(v___x_1075_, 5);
v_recordedDeps_1082_ = lean_ctor_get(v___x_1075_, 6);
v_messages_1083_ = lean_ctor_get(v___x_1075_, 7);
v_infoState_1084_ = lean_ctor_get(v___x_1075_, 8);
v_snapshotTasks_1085_ = lean_ctor_get(v___x_1075_, 9);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1087_ = v___x_1075_;
v_isShared_1088_ = v_isSharedCheck_1115_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snapshotTasks_1085_);
lean_inc(v_infoState_1084_);
lean_inc(v_messages_1083_);
lean_inc(v_recordedDeps_1082_);
lean_inc(v_cache_1081_);
lean_inc(v_traceState_1076_);
lean_inc(v_auxDeclNGen_1080_);
lean_inc(v_ngen_1079_);
lean_inc(v_nextMacroScope_1078_);
lean_inc(v_env_1077_);
lean_dec(v___x_1075_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1115_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint64_t v_tid_1089_; lean_object* v_traces_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1114_; 
v_tid_1089_ = lean_ctor_get_uint64(v_traceState_1076_, sizeof(void*)*1);
v_traces_1090_ = lean_ctor_get(v_traceState_1076_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_traceState_1076_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1092_ = v_traceState_1076_;
v_isShared_1093_ = v_isSharedCheck_1114_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_traces_1090_);
lean_dec(v_traceState_1076_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1114_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; double v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1097_ = 0;
v___x_1098_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1099_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1099_, 0, v_cls_1062_);
lean_ctor_set(v___x_1099_, 1, v___x_1095_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set_float(v___x_1099_, sizeof(void*)*3, v___x_1096_);
lean_ctor_set_float(v___x_1099_, sizeof(void*)*3 + 8, v___x_1096_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*3 + 16, v___x_1097_);
v___x_1100_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1101_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v_a_1071_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
lean_inc(v_ref_1069_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_ref_1069_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_PersistentArray_push___redArg(v_traces_1090_, v___x_1102_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1103_);
v___x_1105_ = v___x_1092_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1103_);
lean_ctor_set_uint64(v_reuseFailAlloc_1113_, sizeof(void*)*1, v_tid_1089_);
v___x_1105_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 4, v___x_1105_);
v___x_1107_ = v___x_1087_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_env_1077_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_nextMacroScope_1078_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_ngen_1079_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_auxDeclNGen_1080_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 5, v_cache_1081_);
lean_ctor_set(v_reuseFailAlloc_1112_, 6, v_recordedDeps_1082_);
lean_ctor_set(v_reuseFailAlloc_1112_, 7, v_messages_1083_);
lean_ctor_set(v_reuseFailAlloc_1112_, 8, v_infoState_1084_);
lean_ctor_set(v_reuseFailAlloc_1112_, 9, v_snapshotTasks_1085_);
v___x_1107_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_st_ref_put(v___y_1067_, v___x_1107_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1094_);
v___x_1110_ = v___x_1073_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1094_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1062_ = stack[0].m_obj;
lean_object* v_msg_1063_ = stack[1].m_obj;
lean_object* v___y_1064_ = stack[2].m_obj;
lean_object* v___y_1065_ = stack[3].m_obj;
lean_object* v___y_1066_ = stack[4].m_obj;
lean_object* v___y_1067_ = stack[5].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1062_, v_msg_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1118_, v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1128_ = l_Lean_stringToMessageData(v___x_1127_);
return v___x_1128_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1129_, lean_object* v_snd_1130_, size_t v_sz_1131_, size_t v___x_1132_, lean_object* v_a_1133_, lean_object* v_fixedArgs_1134_, lean_object* v_fst_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_wfRel_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v_a_1155_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v_toCold_1305_; lean_object* v_options_1306_; uint8_t v_hasTrace_1307_; 
v_toCold_1305_ = lean_ctor_get(v___y_1144_, 0);
v_options_1306_ = lean_ctor_get(v_toCold_1305_, 2);
v_hasTrace_1307_ = lean_ctor_get_uint8(v_options_1306_, sizeof(void*)*1);
if (v_hasTrace_1307_ == 0)
{
lean_dec(v___x_1138_);
v___y_1281_ = v___y_1140_;
v___y_1282_ = v___y_1141_;
v___y_1283_ = v___y_1142_;
v___y_1284_ = v___y_1143_;
v___y_1285_ = v___y_1144_;
v___y_1286_ = v___y_1145_;
goto v___jp_1280_;
}
else
{
lean_object* v_inheritedTraceOptions_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_inheritedTraceOptions_1308_ = lean_ctor_get(v_toCold_1305_, 11);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
lean_inc(v___x_1138_);
v___x_1310_ = l_Lean_Name_append(v___x_1309_, v___x_1138_);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1308_, v_options_1306_, v___x_1310_);
lean_dec(v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec(v___x_1138_);
v___y_1281_ = v___y_1140_;
v___y_1282_ = v___y_1141_;
v___y_1283_ = v___y_1142_;
v___y_1284_ = v___y_1143_;
v___y_1285_ = v___y_1144_;
v___y_1286_ = v___y_1145_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1139_);
v___x_1313_ = l_Lean_MessageData_ofExpr(v_wfRel_1139_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1138_, v___x_1314_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec_ref_known(v___x_1315_, 1);
v___y_1281_ = v___y_1140_;
v___y_1282_ = v___y_1141_;
v___y_1283_ = v___y_1142_;
v___y_1284_ = v___y_1143_;
v___y_1285_ = v___y_1144_;
v___y_1286_ = v___y_1145_;
goto v___jp_1280_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_wfRel_1139_);
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_fst_1135_);
lean_dec_ref(v_fixedArgs_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_fst_1129_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
v___jp_1147_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v___x_1156_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1148_, v___y_1152_, v___y_1150_);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1164_);
v___x_1158_ = v___x_1156_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v___x_1156_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 1);
lean_ctor_set(v___x_1158_, 0, v_a_1155_);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
v___jp_1165_:
{
if (lean_obj_tag(v___y_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v_env_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_a_1174_ = lean_ctor_get(v___y_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___y_1173_, 1);
v___x_1175_ = lean_st_ref_get(v___y_1168_);
v_env_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_ref_n(v_env_1176_, 2);
lean_dec(v___x_1175_);
v___x_1177_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1166_, v___y_1170_, v___y_1168_);
lean_dec_ref(v___x_1177_);
v___x_1178_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1176_, v_a_1174_, v___y_1169_, v___y_1168_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1239_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1239_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1239_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v_nextMacroScope_1185_; lean_object* v_ngen_1186_; lean_object* v_auxDeclNGen_1187_; lean_object* v_traceState_1188_; lean_object* v_recordedDeps_1189_; lean_object* v_messages_1190_; lean_object* v_infoState_1191_; lean_object* v_snapshotTasks_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1237_; 
v___x_1183_ = lean_st_ref_take(v___y_1168_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
v_nextMacroScope_1185_ = lean_ctor_get(v___x_1183_, 1);
v_ngen_1186_ = lean_ctor_get(v___x_1183_, 2);
v_auxDeclNGen_1187_ = lean_ctor_get(v___x_1183_, 3);
v_traceState_1188_ = lean_ctor_get(v___x_1183_, 4);
v_recordedDeps_1189_ = lean_ctor_get(v___x_1183_, 6);
v_messages_1190_ = lean_ctor_get(v___x_1183_, 7);
v_infoState_1191_ = lean_ctor_get(v___x_1183_, 8);
v_snapshotTasks_1192_ = lean_ctor_get(v___x_1183_, 9);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1183_, 5);
lean_dec(v_unused_1238_);
v___x_1194_ = v___x_1183_;
v_isShared_1195_ = v_isSharedCheck_1237_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snapshotTasks_1192_);
lean_inc(v_infoState_1191_);
lean_inc(v_messages_1190_);
lean_inc(v_recordedDeps_1189_);
lean_inc(v_traceState_1188_);
lean_inc(v_auxDeclNGen_1187_);
lean_inc(v_ngen_1186_);
lean_inc(v_nextMacroScope_1185_);
lean_inc(v_env_1184_);
lean_dec(v___x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1237_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = l_Lean_copyExtraModUses(v_env_1176_, v_env_1184_);
v___x_1197_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 5, v___x_1197_);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_nextMacroScope_1185_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_ngen_1186_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_auxDeclNGen_1187_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_traceState_1188_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_recordedDeps_1189_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_messages_1190_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_infoState_1191_);
lean_ctor_set(v_reuseFailAlloc_1236_, 9, v_snapshotTasks_1192_);
v___x_1199_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_mctx_1202_; lean_object* v_zetaDeltaFVarIds_1203_; lean_object* v_postponed_1204_; lean_object* v_diag_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1234_; 
v___x_1200_ = lean_st_ref_put(v___y_1168_, v___x_1199_);
v___x_1201_ = lean_st_ref_take(v___y_1170_);
v_mctx_1202_ = lean_ctor_get(v___x_1201_, 0);
v_zetaDeltaFVarIds_1203_ = lean_ctor_get(v___x_1201_, 2);
v_postponed_1204_ = lean_ctor_get(v___x_1201_, 3);
v_diag_1205_ = lean_ctor_get(v___x_1201_, 4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1201_, 1);
lean_dec(v_unused_1235_);
v___x_1207_ = v___x_1201_;
v_isShared_1208_ = v_isSharedCheck_1234_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_diag_1205_);
lean_inc(v_postponed_1204_);
lean_inc(v_zetaDeltaFVarIds_1203_);
lean_inc(v_mctx_1202_);
lean_dec(v___x_1201_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1234_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_mctx_1202_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_zetaDeltaFVarIds_1203_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_postponed_1204_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_diag_1205_);
v___x_1211_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v_ref_1213_; uint8_t v_kind_1214_; lean_object* v_levelParams_1215_; lean_object* v_modifiers_1216_; lean_object* v_declName_1217_; lean_object* v_binders_1218_; lean_object* v_numSectionVars_1219_; lean_object* v_type_1220_; lean_object* v_termination_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1231_; 
v___x_1212_ = lean_st_ref_put(v___y_1170_, v___x_1211_);
v_ref_1213_ = lean_ctor_get(v_fst_1129_, 0);
v_kind_1214_ = lean_ctor_get_uint8(v_fst_1129_, sizeof(void*)*9);
v_levelParams_1215_ = lean_ctor_get(v_fst_1129_, 1);
v_modifiers_1216_ = lean_ctor_get(v_fst_1129_, 2);
v_declName_1217_ = lean_ctor_get(v_fst_1129_, 3);
v_binders_1218_ = lean_ctor_get(v_fst_1129_, 4);
v_numSectionVars_1219_ = lean_ctor_get(v_fst_1129_, 5);
v_type_1220_ = lean_ctor_get(v_fst_1129_, 6);
v_termination_1221_ = lean_ctor_get(v_fst_1129_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_fst_1129_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_fst_1129_, 7);
lean_dec(v_unused_1232_);
v___x_1223_ = v_fst_1129_;
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_termination_1221_);
lean_inc(v_type_1220_);
lean_inc(v_numSectionVars_1219_);
lean_inc(v_binders_1218_);
lean_inc(v_declName_1217_);
lean_inc(v_modifiers_1216_);
lean_inc(v_levelParams_1215_);
lean_inc(v_ref_1213_);
lean_dec(v_fst_1129_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1231_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 7, v_a_1179_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_ref_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_levelParams_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_modifiers_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_declName_1217_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_binders_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_numSectionVars_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_type_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_a_1179_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_termination_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*9, v_kind_1214_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1226_);
v___x_1228_ = v___x_1181_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
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
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_env_1176_);
lean_dec_ref(v_fst_1129_);
v_a_1240_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1178_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1178_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; 
lean_dec_ref(v_fst_1129_);
v_a_1248_ = lean_ctor_get(v___y_1173_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___y_1173_, 1);
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1167_;
v___y_1150_ = v___y_1168_;
v___y_1151_ = v___y_1169_;
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
v___y_1154_ = v___y_1172_;
v_a_1155_ = v_a_1248_;
goto v___jp_1147_;
}
}
v___jp_1249_:
{
lean_object* v___x_1256_; lean_object* v_env_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_st_ref_get(v___y_1255_);
v_env_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_env_1257_);
lean_dec(v___x_1256_);
v___x_1258_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1130_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1258_, 1);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1131_, v___x_1132_, v_a_1133_);
lean_inc_ref(v_fst_1129_);
v___x_1260_ = l_Lean_Elab_WF_mkFix(v_fst_1129_, v_fixedArgs_1134_, v_fst_1135_, v_wfRel_1139_, v___x_1136_, v___x_1259_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1261_, v___y_1254_, v___y_1255_);
v___y_1166_ = v_env_1257_;
v___y_1167_ = v___y_1251_;
v___y_1168_ = v___y_1255_;
v___y_1169_ = v___y_1254_;
v___y_1170_ = v___y_1253_;
v___y_1171_ = v___y_1250_;
v___y_1172_ = v___y_1252_;
v___y_1173_ = v___x_1262_;
goto v___jp_1165_;
}
else
{
v___y_1166_ = v_env_1257_;
v___y_1167_ = v___y_1251_;
v___y_1168_ = v___y_1255_;
v___y_1169_ = v___y_1254_;
v___y_1170_ = v___y_1253_;
v___y_1171_ = v___y_1250_;
v___y_1172_ = v___y_1252_;
v___y_1173_ = v___x_1260_;
goto v___jp_1165_;
}
}
else
{
lean_object* v_a_1263_; 
lean_dec_ref(v_wfRel_1139_);
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_fst_1135_);
lean_dec_ref(v_fixedArgs_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_fst_1129_);
v_a_1263_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1258_, 1);
v___y_1148_ = v_env_1257_;
v___y_1149_ = v___y_1251_;
v___y_1150_ = v___y_1255_;
v___y_1151_ = v___y_1254_;
v___y_1152_ = v___y_1253_;
v___y_1153_ = v___y_1250_;
v___y_1154_ = v___y_1252_;
v_a_1155_ = v_a_1263_;
goto v___jp_1147_;
}
}
v___jp_1264_:
{
if (lean_obj_tag(v___y_1271_) == 0)
{
lean_dec_ref_known(v___y_1271_, 1);
v___y_1250_ = v___y_1268_;
v___y_1251_ = v___y_1270_;
v___y_1252_ = v___y_1267_;
v___y_1253_ = v___y_1266_;
v___y_1254_ = v___y_1265_;
v___y_1255_ = v___y_1269_;
goto v___jp_1249_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_wfRel_1139_);
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_fst_1135_);
lean_dec_ref(v_fixedArgs_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_fst_1129_);
v_a_1272_ = lean_ctor_get(v___y_1271_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___y_1271_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___y_1271_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___y_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
v___jp_1280_:
{
lean_object* v___x_1287_; 
lean_inc_ref(v_wfRel_1139_);
v___x_1287_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1139_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
if (lean_obj_tag(v_a_1288_) == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_get_size(v_a_1133_);
v___x_1291_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
v___y_1250_ = v___y_1281_;
v___y_1251_ = v___y_1282_;
v___y_1252_ = v___y_1283_;
v___y_1253_ = v___y_1284_;
v___y_1254_ = v___y_1285_;
v___y_1255_ = v___y_1286_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1292_ == 0)
{
if (v___x_1291_ == 0)
{
v___y_1250_ = v___y_1281_;
v___y_1251_ = v___y_1282_;
v___y_1252_ = v___y_1283_;
v___y_1253_ = v___y_1284_;
v___y_1254_ = v___y_1285_;
v___y_1255_ = v___y_1286_;
goto v___jp_1249_;
}
else
{
size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_usize_of_nat(v___x_1290_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1290_, v_a_1133_, v___x_1132_, v___x_1293_, v___x_1137_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v___y_1265_ = v___y_1285_;
v___y_1266_ = v___y_1284_;
v___y_1267_ = v___y_1283_;
v___y_1268_ = v___y_1281_;
v___y_1269_ = v___y_1286_;
v___y_1270_ = v___y_1282_;
v___y_1271_ = v___x_1294_;
goto v___jp_1264_;
}
}
else
{
size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_usize_of_nat(v___x_1290_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1290_, v_a_1133_, v___x_1132_, v___x_1295_, v___x_1137_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v___y_1265_ = v___y_1285_;
v___y_1266_ = v___y_1284_;
v___y_1267_ = v___y_1283_;
v___y_1268_ = v___y_1281_;
v___y_1269_ = v___y_1286_;
v___y_1270_ = v___y_1282_;
v___y_1271_ = v___x_1296_;
goto v___jp_1264_;
}
}
}
else
{
lean_dec_ref_known(v_a_1288_, 1);
v___y_1250_ = v___y_1281_;
v___y_1251_ = v___y_1282_;
v___y_1252_ = v___y_1283_;
v___y_1253_ = v___y_1284_;
v___y_1254_ = v___y_1285_;
v___y_1255_ = v___y_1286_;
goto v___jp_1249_;
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_wfRel_1139_);
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_fst_1135_);
lean_dec_ref(v_fixedArgs_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_fst_1129_);
v_a_1297_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1287_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1287_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1129_ = stack[0].m_obj;
lean_object* v_snd_1130_ = stack[1].m_obj;
size_t v_sz_1131_ = stack[2].m_num;
size_t v___x_1132_ = stack[3].m_num;
lean_object* v_a_1133_ = stack[4].m_obj;
lean_object* v_fixedArgs_1134_ = stack[5].m_obj;
lean_object* v_fst_1135_ = stack[6].m_obj;
lean_object* v___x_1136_ = stack[7].m_obj;
lean_object* v___x_1137_ = stack[8].m_obj;
lean_object* v___x_1138_ = stack[9].m_obj;
lean_object* v_wfRel_1139_ = stack[10].m_obj;
lean_object* v___y_1140_ = stack[11].m_obj;
lean_object* v___y_1141_ = stack[12].m_obj;
lean_object* v___y_1142_ = stack[13].m_obj;
lean_object* v___y_1143_ = stack[14].m_obj;
lean_object* v___y_1144_ = stack[15].m_obj;
lean_object* v___y_1145_ = stack[16].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1129_, v_snd_1130_, v_sz_1131_, v___x_1132_, v_a_1133_, v_fixedArgs_1134_, v_fst_1135_, v___x_1136_, v___x_1137_, v___x_1138_, v_wfRel_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1325_ = _args[0];
lean_object* v_snd_1326_ = _args[1];
lean_object* v_sz_1327_ = _args[2];
lean_object* v___x_1328_ = _args[3];
lean_object* v_a_1329_ = _args[4];
lean_object* v_fixedArgs_1330_ = _args[5];
lean_object* v_fst_1331_ = _args[6];
lean_object* v___x_1332_ = _args[7];
lean_object* v___x_1333_ = _args[8];
lean_object* v___x_1334_ = _args[9];
lean_object* v_wfRel_1335_ = _args[10];
lean_object* v___y_1336_ = _args[11];
lean_object* v___y_1337_ = _args[12];
lean_object* v___y_1338_ = _args[13];
lean_object* v___y_1339_ = _args[14];
lean_object* v___y_1340_ = _args[15];
lean_object* v___y_1341_ = _args[16];
lean_object* v___y_1342_ = _args[17];
_start:
{
size_t v_sz_boxed_1343_; size_t v___x_45747__boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v___x_45747__boxed_1344_ = lean_unbox_usize(v___x_1328_);
lean_dec(v___x_1328_);
v_res_1345_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1325_, v_snd_1326_, v_sz_boxed_1343_, v___x_45747__boxed_1344_, v_a_1329_, v_fixedArgs_1330_, v_fst_1331_, v___x_1332_, v___x_1333_, v___x_1334_, v_wfRel_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec_ref(v_snd_1326_);
return v_res_1345_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1349_, size_t v___x_1350_, lean_object* v_a_1351_, lean_object* v_fst_1352_, lean_object* v_snd_1353_, lean_object* v_fst_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v_declName_1357_, lean_object* v_fst_1358_, lean_object* v_wf_1359_, lean_object* v_fixedArgs_1360_, lean_object* v_type_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_whnfForall(v_type_1361_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___x_1384_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1384_ = l_Lean_Expr_isForall(v_a_1370_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_fixedArgs_1360_);
lean_dec_ref(v_wf_1359_);
lean_dec_ref(v_fst_1358_);
lean_dec(v_declName_1357_);
lean_dec(v___x_1356_);
lean_dec_ref(v_fst_1354_);
lean_dec_ref(v_snd_1353_);
lean_dec_ref(v_fst_1352_);
lean_dec_ref(v_a_1351_);
v___x_1385_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1386_ = l_Lean_MessageData_ofExpr(v_a_1370_);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1387_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
v___y_1372_ = v___y_1362_;
v___y_1373_ = v___y_1363_;
v___y_1374_ = v___y_1364_;
v___y_1375_ = v___y_1365_;
v___y_1376_ = v___y_1366_;
v___y_1377_ = v___y_1367_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; 
v___x_1378_ = l_Lean_Expr_bindingDomain_x21(v_a_1370_);
lean_dec(v_a_1370_);
lean_inc_ref(v_a_1351_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_1349_, v___x_1350_, v_a_1351_);
v___x_1380_ = lean_box_usize(v_sz_1349_);
v___x_1381_ = lean_box_usize(v___x_1350_);
lean_inc_ref(v___x_1379_);
lean_inc_ref(v_fst_1354_);
lean_inc_ref(v_fixedArgs_1360_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1382_, 0, v_fst_1352_);
lean_closure_set(v___f_1382_, 1, v_snd_1353_);
lean_closure_set(v___f_1382_, 2, v___x_1380_);
lean_closure_set(v___f_1382_, 3, v___x_1381_);
lean_closure_set(v___f_1382_, 4, v_a_1351_);
lean_closure_set(v___f_1382_, 5, v_fixedArgs_1360_);
lean_closure_set(v___f_1382_, 6, v_fst_1354_);
lean_closure_set(v___f_1382_, 7, v___x_1379_);
lean_closure_set(v___f_1382_, 8, v___x_1355_);
lean_closure_set(v___f_1382_, 9, v___x_1356_);
v___x_1383_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1379_, v_declName_1357_, v_fst_1358_, v_fixedArgs_1360_, v_fst_1354_, v___x_1378_, v_wf_1359_, v___f_1382_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1383_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_fixedArgs_1360_);
lean_dec_ref(v_wf_1359_);
lean_dec_ref(v_fst_1358_);
lean_dec(v_declName_1357_);
lean_dec(v___x_1356_);
lean_dec_ref(v_fst_1354_);
lean_dec_ref(v_snd_1353_);
lean_dec_ref(v_fst_1352_);
lean_dec_ref(v_a_1351_);
v_a_1397_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1369_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1369_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1349_ = stack[0].m_num;
size_t v___x_1350_ = stack[1].m_num;
lean_object* v_a_1351_ = stack[2].m_obj;
lean_object* v_fst_1352_ = stack[3].m_obj;
lean_object* v_snd_1353_ = stack[4].m_obj;
lean_object* v_fst_1354_ = stack[5].m_obj;
lean_object* v___x_1355_ = stack[6].m_obj;
lean_object* v___x_1356_ = stack[7].m_obj;
lean_object* v_declName_1357_ = stack[8].m_obj;
lean_object* v_fst_1358_ = stack[9].m_obj;
lean_object* v_wf_1359_ = stack[10].m_obj;
lean_object* v_fixedArgs_1360_ = stack[11].m_obj;
lean_object* v_type_1361_ = stack[12].m_obj;
lean_object* v___y_1362_ = stack[13].m_obj;
lean_object* v___y_1363_ = stack[14].m_obj;
lean_object* v___y_1364_ = stack[15].m_obj;
lean_object* v___y_1365_ = stack[16].m_obj;
lean_object* v___y_1366_ = stack[17].m_obj;
lean_object* v___y_1367_ = stack[18].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_1349_, v___x_1350_, v_a_1351_, v_fst_1352_, v_snd_1353_, v_fst_1354_, v___x_1355_, v___x_1356_, v_declName_1357_, v_fst_1358_, v_wf_1359_, v_fixedArgs_1360_, v_type_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1406_ = _args[0];
lean_object* v___x_1407_ = _args[1];
lean_object* v_a_1408_ = _args[2];
lean_object* v_fst_1409_ = _args[3];
lean_object* v_snd_1410_ = _args[4];
lean_object* v_fst_1411_ = _args[5];
lean_object* v___x_1412_ = _args[6];
lean_object* v___x_1413_ = _args[7];
lean_object* v_declName_1414_ = _args[8];
lean_object* v_fst_1415_ = _args[9];
lean_object* v_wf_1416_ = _args[10];
lean_object* v_fixedArgs_1417_ = _args[11];
lean_object* v_type_1418_ = _args[12];
lean_object* v___y_1419_ = _args[13];
lean_object* v___y_1420_ = _args[14];
lean_object* v___y_1421_ = _args[15];
lean_object* v___y_1422_ = _args[16];
lean_object* v___y_1423_ = _args[17];
lean_object* v___y_1424_ = _args[18];
lean_object* v___y_1425_ = _args[19];
_start:
{
size_t v_sz_boxed_1426_; size_t v___x_46288__boxed_1427_; lean_object* v_res_1428_; 
v_sz_boxed_1426_ = lean_unbox_usize(v_sz_1406_);
lean_dec(v_sz_1406_);
v___x_46288__boxed_1427_ = lean_unbox_usize(v___x_1407_);
lean_dec(v___x_1407_);
v_res_1428_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1426_, v___x_46288__boxed_1427_, v_a_1408_, v_fst_1409_, v_snd_1410_, v_fst_1411_, v___x_1412_, v___x_1413_, v_declName_1414_, v_fst_1415_, v_wf_1416_, v_fixedArgs_1417_, v_type_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1428_;
}
}
lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1429_, lean_object* v_fst_1430_, lean_object* v_fst_1431_, lean_object* v_fst_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Elab_WF_guessLex(v_a_1429_, v_fst_1430_, v_fst_1431_, v_fst_1432_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1429_ = stack[0].m_obj;
lean_object* v_fst_1430_ = stack[1].m_obj;
lean_object* v_fst_1431_ = stack[2].m_obj;
lean_object* v_fst_1432_ = stack[3].m_obj;
lean_object* v___y_1433_ = stack[4].m_obj;
lean_object* v___y_1434_ = stack[5].m_obj;
lean_object* v___y_1435_ = stack[6].m_obj;
lean_object* v___y_1436_ = stack[7].m_obj;
lean_object* v___y_1437_ = stack[8].m_obj;
lean_object* v___y_1438_ = stack[9].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1429_, v_fst_1430_, v_fst_1431_, v_fst_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1442_, lean_object* v_fst_1443_, lean_object* v_fst_1444_, lean_object* v_fst_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1442_, v_fst_1443_, v_fst_1444_, v_fst_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1453_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_env_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v_env_1464_; lean_object* v_a_1466_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1463_ = lean_st_ref_get(v___y_1461_);
v_env_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc_ref(v_env_1464_);
lean_dec(v___x_1463_);
v___x_1476_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1454_, v___y_1459_, v___y_1461_);
lean_dec_ref(v___x_1476_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
v___x_1477_ = lean_apply_7(v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1464_, v___y_1459_, v___y_1461_);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1487_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_a_1478_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1478_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1488_; 
v_a_1488_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1477_, 1);
v_a_1466_ = v_a_1488_;
goto v___jp_1465_;
}
v___jp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v___x_1467_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1464_, v___y_1459_, v___y_1461_);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1467_, 0);
lean_dec(v_unused_1475_);
v___x_1469_ = v___x_1467_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v___x_1467_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 1);
lean_ctor_set(v___x_1469_, 0, v_a_1466_);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1466_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1454_ = stack[0].m_obj;
lean_object* v_x_1455_ = stack[1].m_obj;
lean_object* v___y_1456_ = stack[2].m_obj;
lean_object* v___y_1457_ = stack[3].m_obj;
lean_object* v___y_1458_ = stack[4].m_obj;
lean_object* v___y_1459_ = stack[5].m_obj;
lean_object* v___y_1460_ = stack[6].m_obj;
lean_object* v___y_1461_ = stack[7].m_obj;
lean_object* v_res_1489_;
v_res_1489_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1454_, v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
stack->m_obj
 = v_res_1489_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_env_1490_, lean_object* v_x_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1490_, v_x_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1499_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1500_, uint8_t v_isExporting_1501_, lean_object* v___x_1502_, lean_object* v___y_1503_, lean_object* v___x_1504_, lean_object* v_a_x3f_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v_env_1508_; lean_object* v_nextMacroScope_1509_; lean_object* v_ngen_1510_; lean_object* v_auxDeclNGen_1511_; lean_object* v_traceState_1512_; lean_object* v_recordedDeps_1513_; lean_object* v_messages_1514_; lean_object* v_infoState_1515_; lean_object* v_snapshotTasks_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1541_; 
v___x_1507_ = lean_st_ref_take(v___y_1500_);
v_env_1508_ = lean_ctor_get(v___x_1507_, 0);
v_nextMacroScope_1509_ = lean_ctor_get(v___x_1507_, 1);
v_ngen_1510_ = lean_ctor_get(v___x_1507_, 2);
v_auxDeclNGen_1511_ = lean_ctor_get(v___x_1507_, 3);
v_traceState_1512_ = lean_ctor_get(v___x_1507_, 4);
v_recordedDeps_1513_ = lean_ctor_get(v___x_1507_, 6);
v_messages_1514_ = lean_ctor_get(v___x_1507_, 7);
v_infoState_1515_ = lean_ctor_get(v___x_1507_, 8);
v_snapshotTasks_1516_ = lean_ctor_get(v___x_1507_, 9);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1507_, 5);
lean_dec(v_unused_1542_);
v___x_1518_ = v___x_1507_;
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snapshotTasks_1516_);
lean_inc(v_infoState_1515_);
lean_inc(v_messages_1514_);
lean_inc(v_recordedDeps_1513_);
lean_inc(v_traceState_1512_);
lean_inc(v_auxDeclNGen_1511_);
lean_inc(v_ngen_1510_);
lean_inc(v_nextMacroScope_1509_);
lean_inc(v_env_1508_);
lean_dec(v___x_1507_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = l_Lean_Environment_setExporting(v_env_1508_, v_isExporting_1501_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 5, v___x_1502_);
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_nextMacroScope_1509_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_ngen_1510_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_auxDeclNGen_1511_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_traceState_1512_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_recordedDeps_1513_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_messages_1514_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_infoState_1515_);
lean_ctor_set(v_reuseFailAlloc_1540_, 9, v_snapshotTasks_1516_);
v___x_1522_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_mctx_1525_; lean_object* v_zetaDeltaFVarIds_1526_; lean_object* v_postponed_1527_; lean_object* v_diag_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1538_; 
v___x_1523_ = lean_st_ref_put(v___y_1500_, v___x_1522_);
v___x_1524_ = lean_st_ref_take(v___y_1503_);
v_mctx_1525_ = lean_ctor_get(v___x_1524_, 0);
v_zetaDeltaFVarIds_1526_ = lean_ctor_get(v___x_1524_, 2);
v_postponed_1527_ = lean_ctor_get(v___x_1524_, 3);
v_diag_1528_ = lean_ctor_get(v___x_1524_, 4);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1524_, 1);
lean_dec(v_unused_1539_);
v___x_1530_ = v___x_1524_;
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_diag_1528_);
lean_inc(v_postponed_1527_);
lean_inc(v_zetaDeltaFVarIds_1526_);
lean_inc(v_mctx_1525_);
lean_dec(v___x_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_box(0);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1504_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_mctx_1525_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_zetaDeltaFVarIds_1526_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_postponed_1527_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_diag_1528_);
v___x_1534_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_st_ref_put(v___y_1503_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1532_);
return v___x_1536_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1500_ = stack[0].m_obj;
uint8_t v_isExporting_1501_ = stack[1].m_num;
lean_object* v___x_1502_ = stack[2].m_obj;
lean_object* v___y_1503_ = stack[3].m_obj;
lean_object* v___x_1504_ = stack[4].m_obj;
lean_object* v_a_x3f_1505_ = stack[5].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1500_, v_isExporting_1501_, v___x_1502_, v___y_1503_, v___x_1504_, v_a_x3f_1505_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1544_, lean_object* v_isExporting_1545_, lean_object* v___x_1546_, lean_object* v___y_1547_, lean_object* v___x_1548_, lean_object* v_a_x3f_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_isExporting_boxed_1551_; lean_object* v_res_1552_; 
v_isExporting_boxed_1551_ = lean_unbox(v_isExporting_1545_);
v_res_1552_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1544_, v_isExporting_boxed_1551_, v___x_1546_, v___y_1547_, v___x_1548_, v_a_x3f_1549_);
lean_dec(v_a_x3f_1549_);
lean_dec(v___y_1547_);
lean_dec(v___y_1544_);
return v_res_1552_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1553_, uint8_t v_isExporting_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_env_1563_; lean_object* v___x_1564_; uint8_t v_isModule_1565_; 
v___x_1562_ = lean_st_ref_get(v___y_1560_);
v_env_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc_ref(v_env_1563_);
lean_dec(v___x_1562_);
v___x_1564_ = l_Lean_Environment_header(v_env_1563_);
v_isModule_1565_ = lean_ctor_get_uint8(v___x_1564_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1564_);
if (v_isModule_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec_ref(v_env_1563_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___x_1566_ = lean_apply_7(v_x_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
return v___x_1566_;
}
else
{
uint8_t v_isExporting_1567_; 
v_isExporting_1567_ = lean_ctor_get_uint8(v_env_1563_, sizeof(void*)*13);
lean_dec_ref(v_env_1563_);
if (v_isExporting_1554_ == 0)
{
if (v_isExporting_1567_ == 0)
{
lean_object* v___x_1634_; 
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___x_1634_ = lean_apply_7(v_x_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
return v___x_1634_;
}
else
{
goto v___jp_1568_;
}
}
else
{
if (v_isExporting_1567_ == 0)
{
goto v___jp_1568_;
}
else
{
lean_object* v___x_1635_; 
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___x_1635_ = lean_apply_7(v_x_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
return v___x_1635_;
}
}
v___jp_1568_:
{
lean_object* v___x_1569_; lean_object* v_env_1570_; lean_object* v_nextMacroScope_1571_; lean_object* v_ngen_1572_; lean_object* v_auxDeclNGen_1573_; lean_object* v_traceState_1574_; lean_object* v_recordedDeps_1575_; lean_object* v_messages_1576_; lean_object* v_infoState_1577_; lean_object* v_snapshotTasks_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1632_; 
v___x_1569_ = lean_st_ref_take(v___y_1560_);
v_env_1570_ = lean_ctor_get(v___x_1569_, 0);
v_nextMacroScope_1571_ = lean_ctor_get(v___x_1569_, 1);
v_ngen_1572_ = lean_ctor_get(v___x_1569_, 2);
v_auxDeclNGen_1573_ = lean_ctor_get(v___x_1569_, 3);
v_traceState_1574_ = lean_ctor_get(v___x_1569_, 4);
v_recordedDeps_1575_ = lean_ctor_get(v___x_1569_, 6);
v_messages_1576_ = lean_ctor_get(v___x_1569_, 7);
v_infoState_1577_ = lean_ctor_get(v___x_1569_, 8);
v_snapshotTasks_1578_ = lean_ctor_get(v___x_1569_, 9);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v___x_1569_, 5);
lean_dec(v_unused_1633_);
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1632_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snapshotTasks_1578_);
lean_inc(v_infoState_1577_);
lean_inc(v_messages_1576_);
lean_inc(v_recordedDeps_1575_);
lean_inc(v_traceState_1574_);
lean_inc(v_auxDeclNGen_1573_);
lean_inc(v_ngen_1572_);
lean_inc(v_nextMacroScope_1571_);
lean_inc(v_env_1570_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1632_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = l_Lean_Environment_setExporting(v_env_1570_, v_isExporting_1554_);
v___x_1583_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 5, v___x_1583_);
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_nextMacroScope_1571_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_ngen_1572_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_auxDeclNGen_1573_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_traceState_1574_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_recordedDeps_1575_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v_messages_1576_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_infoState_1577_);
lean_ctor_set(v_reuseFailAlloc_1631_, 9, v_snapshotTasks_1578_);
v___x_1585_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_mctx_1588_; lean_object* v_zetaDeltaFVarIds_1589_; lean_object* v_postponed_1590_; lean_object* v_diag_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1629_; 
v___x_1586_ = lean_st_ref_put(v___y_1560_, v___x_1585_);
v___x_1587_ = lean_st_ref_take(v___y_1558_);
v_mctx_1588_ = lean_ctor_get(v___x_1587_, 0);
v_zetaDeltaFVarIds_1589_ = lean_ctor_get(v___x_1587_, 2);
v_postponed_1590_ = lean_ctor_get(v___x_1587_, 3);
v_diag_1591_ = lean_ctor_get(v___x_1587_, 4);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v___x_1587_, 1);
lean_dec(v_unused_1630_);
v___x_1593_ = v___x_1587_;
v_isShared_1594_ = v_isSharedCheck_1629_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_diag_1591_);
lean_inc(v_postponed_1590_);
lean_inc(v_zetaDeltaFVarIds_1589_);
lean_inc(v_mctx_1588_);
lean_dec(v___x_1587_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1629_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_mctx_1588_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_zetaDeltaFVarIds_1589_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_postponed_1590_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_diag_1591_);
v___x_1597_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v_r_1599_; 
v___x_1598_ = lean_st_ref_put(v___y_1558_, v___x_1597_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v_r_1599_ = lean_apply_7(v_x_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
if (lean_obj_tag(v_r_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1616_; 
v_a_1600_ = lean_ctor_get(v_r_1599_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_r_1599_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1602_ = v_r_1599_;
v_isShared_1603_ = v_isSharedCheck_1616_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_r_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1616_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
lean_inc(v_a_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 1);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v___x_1606_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1560_, v_isExporting_1567_, v___x_1583_, v___y_1558_, v___x_1595_, v___x_1605_);
lean_dec_ref(v___x_1605_);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1614_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_a_1600_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1600_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1617_ = lean_ctor_get(v_r_1599_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v_r_1599_, 1);
v___x_1618_ = lean_box(0);
v___x_1619_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1560_, v_isExporting_1567_, v___x_1583_, v___y_1558_, v___x_1595_, v___x_1618_);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1619_, 0);
lean_dec(v_unused_1627_);
v___x_1621_ = v___x_1619_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1619_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 1);
lean_ctor_set(v___x_1621_, 0, v_a_1617_);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1617_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1553_ = stack[0].m_obj;
uint8_t v_isExporting_1554_ = stack[1].m_num;
lean_object* v___y_1555_ = stack[2].m_obj;
lean_object* v___y_1556_ = stack[3].m_obj;
lean_object* v___y_1557_ = stack[4].m_obj;
lean_object* v___y_1558_ = stack[5].m_obj;
lean_object* v___y_1559_ = stack[6].m_obj;
lean_object* v___y_1560_ = stack[7].m_obj;
lean_object* v_res_1636_;
v_res_1636_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1553_, v_isExporting_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1637_, lean_object* v_isExporting_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_isExporting_boxed_1646_; lean_object* v_res_1647_; 
v_isExporting_boxed_1646_ = lean_unbox(v_isExporting_1638_);
v_res_1647_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1637_, v_isExporting_boxed_1646_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1647_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1648_, uint8_t v_when_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
if (v_when_1649_ == 0)
{
lean_object* v___x_1657_; 
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
v___x_1657_ = lean_apply_7(v_x_1648_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, lean_box(0));
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = 0;
v___x_1659_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1648_, v___x_1658_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1659_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1648_ = stack[0].m_obj;
uint8_t v_when_1649_ = stack[1].m_num;
lean_object* v___y_1650_ = stack[2].m_obj;
lean_object* v___y_1651_ = stack[3].m_obj;
lean_object* v___y_1652_ = stack[4].m_obj;
lean_object* v___y_1653_ = stack[5].m_obj;
lean_object* v___y_1654_ = stack[6].m_obj;
lean_object* v___y_1655_ = stack[7].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1648_, v_when_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1661_, lean_object* v_when_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v_when_boxed_1670_; lean_object* v_res_1671_; 
v_when_boxed_1670_ = lean_unbox(v_when_1662_);
v_res_1671_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1661_, v_when_boxed_1670_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1671_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_bs_1674_);
return v___x_1679_;
}
else
{
lean_object* v_v_1680_; lean_object* v_ref_1681_; uint8_t v_kind_1682_; lean_object* v_levelParams_1683_; lean_object* v_modifiers_1684_; lean_object* v_declName_1685_; lean_object* v_binders_1686_; lean_object* v_numSectionVars_1687_; lean_object* v_type_1688_; lean_object* v_value_1689_; lean_object* v_termination_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1713_; 
v_v_1680_ = lean_array_uget(v_bs_1674_, v_i_1673_);
v_ref_1681_ = lean_ctor_get(v_v_1680_, 0);
v_kind_1682_ = lean_ctor_get_uint8(v_v_1680_, sizeof(void*)*9);
v_levelParams_1683_ = lean_ctor_get(v_v_1680_, 1);
v_modifiers_1684_ = lean_ctor_get(v_v_1680_, 2);
v_declName_1685_ = lean_ctor_get(v_v_1680_, 3);
v_binders_1686_ = lean_ctor_get(v_v_1680_, 4);
v_numSectionVars_1687_ = lean_ctor_get(v_v_1680_, 5);
v_type_1688_ = lean_ctor_get(v_v_1680_, 6);
v_value_1689_ = lean_ctor_get(v_v_1680_, 7);
v_termination_1690_ = lean_ctor_get(v_v_1680_, 8);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_v_1680_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1692_ = v_v_1680_;
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_termination_1690_);
lean_inc(v_value_1689_);
lean_inc(v_type_1688_);
lean_inc(v_numSectionVars_1687_);
lean_inc(v_binders_1686_);
lean_inc(v_declName_1685_);
lean_inc(v_modifiers_1684_);
lean_inc(v_levelParams_1683_);
lean_inc(v_ref_1681_);
lean_dec(v_v_1680_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v_bs_x27_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v_bs_x27_1695_ = lean_array_uset(v_bs_1674_, v_i_1673_, v___x_1694_);
v___x_1696_ = l_Lean_Elab_WF_floatRecApp(v_value_1689_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 7, v_a_1697_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_ref_1681_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_levelParams_1683_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_modifiers_1684_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_declName_1685_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_binders_1686_);
lean_ctor_set(v_reuseFailAlloc_1704_, 5, v_numSectionVars_1687_);
lean_ctor_set(v_reuseFailAlloc_1704_, 6, v_type_1688_);
lean_ctor_set(v_reuseFailAlloc_1704_, 7, v_a_1697_);
lean_ctor_set(v_reuseFailAlloc_1704_, 8, v_termination_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*9, v_kind_1682_);
v___x_1699_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1673_, v___x_1700_);
v___x_1702_ = lean_array_uset(v_bs_x27_1695_, v_i_1673_, v___x_1699_);
v_i_1673_ = v___x_1701_;
v_bs_1674_ = v___x_1702_;
goto _start;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_bs_x27_1695_);
lean_del_object(v___x_1692_);
lean_dec_ref(v_termination_1690_);
lean_dec_ref(v_type_1688_);
lean_dec(v_numSectionVars_1687_);
lean_dec(v_binders_1686_);
lean_dec(v_declName_1685_);
lean_dec_ref(v_modifiers_1684_);
lean_dec(v_levelParams_1683_);
lean_dec(v_ref_1681_);
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1696_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1696_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1672_ = stack[0].m_num;
size_t v_i_1673_ = stack[1].m_num;
lean_object* v_bs_1674_ = stack[2].m_obj;
lean_object* v___y_1675_ = stack[3].m_obj;
lean_object* v___y_1676_ = stack[4].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1672_, v_i_1673_, v_bs_1674_, v___y_1675_, v___y_1676_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
size_t v_sz_boxed_1721_; size_t v_i_boxed_1722_; lean_object* v_res_1723_; 
v_sz_boxed_1721_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1722_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_boxed_1721_, v_i_boxed_1722_, v_bs_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_bs_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_bs_1726_);
return v___x_1728_;
}
else
{
lean_object* v_v_1729_; 
v_v_1729_ = lean_array_uget_borrowed(v_bs_1726_, v_i_1725_);
if (lean_obj_tag(v_v_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_bs_1726_);
v___x_1730_ = lean_box(0);
return v___x_1730_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v_bs_x27_1733_; size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v_val_1731_ = lean_ctor_get(v_v_1729_, 0);
lean_inc(v_val_1731_);
v___x_1732_ = lean_unsigned_to_nat(0u);
v_bs_x27_1733_ = lean_array_uset(v_bs_1726_, v_i_1725_, v___x_1732_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1725_, v___x_1734_);
v___x_1736_ = lean_array_uset(v_bs_x27_1733_, v_i_1725_, v_val_1731_);
v_i_1725_ = v___x_1735_;
v_bs_1726_ = v___x_1736_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1724_ = stack[0].m_num;
size_t v_i_1725_ = stack[1].m_num;
lean_object* v_bs_1726_ = stack[2].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1724_, v_i_1725_, v_bs_1726_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_bs_1741_){
_start:
{
size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_1742_, v_i_boxed_1743_, v_bs_1741_);
return v_res_1744_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_bs_1747_);
return v___x_1754_;
}
else
{
uint8_t v___x_1755_; lean_object* v_v_1756_; lean_object* v___x_1757_; lean_object* v_bs_x27_1758_; lean_object* v___x_1759_; 
v___x_1755_ = 0;
v_v_1756_ = lean_array_uget(v_bs_1747_, v_i_1746_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v_bs_x27_1758_ = lean_array_uset(v_bs_1747_, v_i_1746_, v___x_1757_);
v___x_1759_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1756_, v___x_1755_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1746_, v___x_1761_);
v___x_1763_ = lean_array_uset(v_bs_x27_1758_, v_i_1746_, v_a_1760_);
v_i_1746_ = v___x_1762_;
v_bs_1747_ = v___x_1763_;
goto _start;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_bs_x27_1758_);
v_a_1765_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1759_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1759_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1745_ = stack[0].m_num;
size_t v_i_1746_ = stack[1].m_num;
lean_object* v_bs_1747_ = stack[2].m_obj;
lean_object* v___y_1748_ = stack[3].m_obj;
lean_object* v___y_1749_ = stack[4].m_obj;
lean_object* v___y_1750_ = stack[5].m_obj;
lean_object* v___y_1751_ = stack[6].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1745_, v_i_1746_, v_bs_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1774_, lean_object* v_i_1775_, lean_object* v_bs_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
size_t v_sz_boxed_1782_; size_t v_i_boxed_1783_; lean_object* v_res_1784_; 
v_sz_boxed_1782_ = lean_unbox_usize(v_sz_1774_);
lean_dec(v_sz_1774_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1782_, v_i_boxed_1783_, v_bs_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1784_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1785_, lean_object* v_as_1786_, size_t v_sz_1787_, size_t v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_a_1796_; uint8_t v___x_1800_; 
v___x_1800_ = lean_usize_dec_lt(v_i_1788_, v_sz_1787_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec(v___x_1785_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_b_1789_);
return v___x_1801_;
}
else
{
lean_object* v_a_1802_; uint8_t v_kind_1803_; lean_object* v_declName_1804_; lean_object* v_type_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_a_1802_ = lean_array_uget_borrowed(v_as_1786_, v_i_1788_);
v_kind_1803_ = lean_ctor_get_uint8(v_a_1802_, sizeof(void*)*9);
v_declName_1804_ = lean_ctor_get(v_a_1802_, 3);
v_type_1805_ = lean_ctor_get(v_a_1802_, 6);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_name_eq(v_declName_1804_, v___x_1785_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1803_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_inc_ref(v_type_1805_);
v___x_1809_ = l_Lean_Meta_isProp(v_type_1805_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; uint8_t v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = lean_unbox(v_a_1810_);
lean_dec(v_a_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
lean_inc(v___x_1785_);
lean_inc(v_a_1802_);
v___x_1812_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1802_, v___x_1785_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_dec_ref_known(v___x_1812_, 1);
v_a_1796_ = v___x_1806_;
goto v___jp_1795_;
}
else
{
lean_dec(v___x_1785_);
return v___x_1812_;
}
}
else
{
v_a_1796_ = v___x_1806_;
goto v___jp_1795_;
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v___x_1785_);
v_a_1813_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1809_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
v_a_1796_ = v___x_1806_;
goto v___jp_1795_;
}
}
else
{
v_a_1796_ = v___x_1806_;
goto v___jp_1795_;
}
}
v___jp_1795_:
{
size_t v___x_1797_; size_t v___x_1798_; 
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1788_, v___x_1797_);
v_i_1788_ = v___x_1798_;
v_b_1789_ = v_a_1796_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1785_ = stack[0].m_obj;
lean_object* v_as_1786_ = stack[1].m_obj;
size_t v_sz_1787_ = stack[2].m_num;
size_t v_i_1788_ = stack[3].m_num;
lean_object* v_b_1789_ = stack[4].m_obj;
lean_object* v___y_1790_ = stack[5].m_obj;
lean_object* v___y_1791_ = stack[6].m_obj;
lean_object* v___y_1792_ = stack[7].m_obj;
lean_object* v___y_1793_ = stack[8].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1785_, v_as_1786_, v_sz_1787_, v_i_1788_, v_b_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
stack->m_obj
 = v_res_1821_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1822_, lean_object* v_as_1823_, lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1822_, v_as_1823_, v_sz_boxed_1832_, v_i_boxed_1833_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_as_1823_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1855_, lean_object* v_preDefs_1856_, lean_object* v_termMeasure_x3fs_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; size_t v_sz_1866_; size_t v___x_1867_; lean_object* v_termMeasures_x3f_1868_; size_t v_sz_1869_; lean_object* v___x_1870_; 
v___x_1865_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_1866_ = lean_array_size(v_termMeasure_x3fs_1857_);
v___x_1867_ = ((size_t)0ULL);
v_termMeasures_x3f_1868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1866_, v___x_1867_, v_termMeasure_x3fs_1857_);
v_sz_1869_ = lean_array_size(v_preDefs_1856_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1869_, v___x_1867_, v_preDefs_1856_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; size_t v_sz_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc_n(v_a_1871_, 2);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = lean_box(0);
v_sz_1886_ = lean_array_size(v_a_1871_);
v___x_1887_ = lean_box_usize(v_sz_1886_);
v___x_1888_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1889_, 0, v_a_1871_);
lean_closure_set(v___f_1889_, 1, v___x_1887_);
lean_closure_set(v___f_1889_, 2, v___x_1888_);
lean_closure_set(v___f_1889_, 3, v___x_1872_);
lean_closure_set(v___f_1889_, 4, v___x_1865_);
v___x_1890_ = lean_st_ref_get(v_a_1863_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_Environment_unlockAsync(v_env_1891_);
v___x_1893_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1892_, v___f_1889_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v_snd_1895_; lean_object* v_fst_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_2081_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v_snd_1895_ = lean_ctor_get(v_a_1894_, 1);
v_fst_1896_ = lean_ctor_get(v_a_1894_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_1894_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_1898_ = v_a_1894_;
v_isShared_1899_ = v_isSharedCheck_2081_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snd_1895_);
lean_inc(v_fst_1896_);
lean_dec(v_a_1894_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_2081_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_fst_1900_; lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_2080_; 
v_fst_1900_ = lean_ctor_get(v_snd_1895_, 0);
v_snd_1901_ = lean_ctor_get(v_snd_1895_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_snd_1895_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_1903_ = v_snd_1895_;
v_isShared_1904_ = v_isSharedCheck_2080_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_inc(v_fst_1900_);
lean_dec(v_snd_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_2080_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
uint8_t v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_wf_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___x_2071_; lean_object* v_a_2072_; uint8_t v___x_2073_; 
lean_inc(v_snd_1901_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1964_, 0, v_snd_1901_);
v___x_1965_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2071_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1965_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = lean_unbox(v_a_2072_);
lean_dec(v_a_2072_);
if (v___x_2073_ == 0)
{
v___y_2034_ = v_a_1858_;
v___y_2035_ = v_a_1859_;
v___y_2036_ = v_a_1860_;
v___y_2037_ = v_a_1861_;
v___y_2038_ = v_a_1862_;
v___y_2039_ = v_a_1863_;
goto v___jp_2033_;
}
else
{
lean_object* v_value_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_value_2074_ = lean_ctor_get(v_snd_1901_, 7);
v___x_2075_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2074_);
v___x_2076_ = l_Lean_MessageData_ofExpr(v_value_2074_);
v___x_2077_ = l_Lean_indentD(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1965_, v___x_2078_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_dec_ref_known(v___x_2079_, 1);
v___y_2034_ = v_a_1858_;
v___y_2035_ = v_a_1859_;
v___y_2036_ = v_a_1860_;
v___y_2037_ = v_a_1861_;
v___y_2038_ = v_a_1862_;
v___y_2039_ = v_a_1863_;
goto v___jp_2033_;
}
else
{
lean_dec_ref(v___f_1964_);
lean_del_object(v___x_1903_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_del_object(v___x_1898_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec(v_termMeasures_x3f_1868_);
lean_dec_ref(v_docCtx_1855_);
return v___x_2079_;
}
}
v___jp_1905_:
{
lean_object* v___x_1915_; 
lean_inc_ref(v___y_1907_);
lean_inc(v_a_1871_);
lean_inc(v_fst_1900_);
lean_inc(v_fst_1896_);
v___x_1915_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1896_, v_fst_1900_, v_a_1871_, v___y_1907_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
lean_inc_ref(v___y_1907_);
lean_inc(v_a_1871_);
lean_inc_ref(v_docCtx_1855_);
v___x_1917_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1855_, v_a_1871_, v_a_1916_, v___y_1907_, v___y_1906_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v_a_1916_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref_known(v___x_1917_, 1);
lean_inc(v_a_1871_);
v___x_1918_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1855_, v_a_1871_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref_known(v___x_1918_, 1);
v___x_1919_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1901_, v___y_1906_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1886_, v___x_1867_, v_a_1871_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_declName_1923_; lean_object* v___x_1924_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc_n(v_a_1922_, 2);
lean_dec_ref_known(v___x_1921_, 1);
v_declName_1923_ = lean_ctor_get(v___y_1907_, 3);
lean_inc_n(v_declName_1923_, 2);
lean_dec_ref(v___y_1907_);
v___x_1924_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1922_, v_declName_1923_, v_fst_1896_, v_fst_1900_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_declName_1925_; lean_object* v_type_1926_; lean_object* v___x_1927_; 
lean_dec_ref_known(v___x_1924_, 1);
v_declName_1925_ = lean_ctor_get(v_a_1920_, 3);
v_type_1926_ = lean_ctor_get(v_a_1920_, 6);
lean_inc(v_declName_1925_);
v___x_1927_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1925_, v___y_1914_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref_known(v___x_1927_, 1);
lean_inc_ref(v_type_1926_);
v___x_1928_ = l_Lean_Meta_isProp(v_type_1926_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_inc(v_declName_1923_);
v___x_1931_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1920_, v_declName_1923_, v___y_1908_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_dec_ref_known(v___x_1931_, 1);
v___y_1874_ = v_a_1922_;
v___y_1875_ = v_declName_1923_;
v___y_1876_ = v___y_1909_;
v___y_1877_ = v___y_1910_;
v___y_1878_ = v___y_1911_;
v___y_1879_ = v___y_1912_;
v___y_1880_ = v___y_1913_;
v___y_1881_ = v___y_1914_;
goto v___jp_1873_;
}
else
{
lean_dec(v_declName_1923_);
lean_dec(v_a_1922_);
return v___x_1931_;
}
}
else
{
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1908_);
v___y_1874_ = v_a_1922_;
v___y_1875_ = v_declName_1923_;
v___y_1876_ = v___y_1909_;
v___y_1877_ = v___y_1910_;
v___y_1878_ = v___y_1911_;
v___y_1879_ = v___y_1912_;
v___y_1880_ = v___y_1913_;
v___y_1881_ = v___y_1914_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_declName_1923_);
lean_dec(v_a_1922_);
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1908_);
v_a_1932_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1928_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_dec(v_declName_1923_);
lean_dec(v_a_1922_);
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1908_);
return v___x_1927_;
}
}
else
{
lean_dec(v_declName_1923_);
lean_dec(v_a_1922_);
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1908_);
return v___x_1924_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1920_);
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
v_a_1940_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1921_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1921_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
v_a_1948_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1919_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1919_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
return v___x_1918_;
}
}
else
{
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec_ref(v_docCtx_1855_);
return v___x_1917_;
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec_ref(v_docCtx_1855_);
v_a_1956_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1915_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1915_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
v___jp_1966_:
{
lean_object* v_declName_1976_; lean_object* v_type_1977_; lean_object* v_numFixed_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; 
v_declName_1976_ = lean_ctor_get(v_snd_1901_, 3);
v_type_1977_ = lean_ctor_get(v_snd_1901_, 6);
v_numFixed_1978_ = lean_ctor_get(v_fst_1896_, 0);
v___x_1979_ = lean_box_usize(v_sz_1886_);
v___x_1980_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1896_);
lean_inc(v_declName_1976_);
lean_inc(v_fst_1900_);
lean_inc(v_snd_1901_);
lean_inc(v_a_1871_);
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1981_, 0, v___x_1979_);
lean_closure_set(v___f_1981_, 1, v___x_1980_);
lean_closure_set(v___f_1981_, 2, v_a_1871_);
lean_closure_set(v___f_1981_, 3, v___y_1967_);
lean_closure_set(v___f_1981_, 4, v_snd_1901_);
lean_closure_set(v___f_1981_, 5, v_fst_1900_);
lean_closure_set(v___f_1981_, 6, v___x_1872_);
lean_closure_set(v___f_1981_, 7, v___x_1965_);
lean_closure_set(v___f_1981_, 8, v_declName_1976_);
lean_closure_set(v___f_1981_, 9, v_fst_1896_);
lean_closure_set(v___f_1981_, 10, v_wf_1969_);
lean_inc(v_numFixed_1978_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_numFixed_1978_);
v___x_1983_ = 0;
lean_inc_ref(v_type_1977_);
v___x_1984_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1977_, v___x_1982_, v___f_1981_, v___x_1983_, v___x_1983_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; uint8_t v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1965_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v___x_1988_ = lean_unbox(v_a_1987_);
lean_dec(v_a_1987_);
if (v___x_1988_ == 0)
{
lean_del_object(v___x_1903_);
lean_del_object(v___x_1898_);
v___y_1906_ = v___x_1983_;
v___y_1907_ = v_a_1985_;
v___y_1908_ = v___y_1968_;
v___y_1909_ = v___y_1970_;
v___y_1910_ = v___y_1971_;
v___y_1911_ = v___y_1972_;
v___y_1912_ = v___y_1973_;
v___y_1913_ = v___y_1974_;
v___y_1914_ = v___y_1975_;
goto v___jp_1905_;
}
else
{
lean_object* v_declName_1989_; lean_object* v_value_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v_declName_1989_ = lean_ctor_get(v_a_1985_, 3);
v_value_1990_ = lean_ctor_get(v_a_1985_, 7);
v___x_1991_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1989_);
v___x_1992_ = l_Lean_MessageData_ofName(v_declName_1989_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 7);
lean_ctor_set(v___x_1903_, 1, v___x_1992_);
lean_ctor_set(v___x_1903_, 0, v___x_1991_);
v___x_1994_ = v___x_1903_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1899_ == 0)
{
lean_ctor_set_tag(v___x_1898_, 7);
lean_ctor_set(v___x_1898_, 1, v___x_1995_);
lean_ctor_set(v___x_1898_, 0, v___x_1994_);
v___x_1997_ = v___x_1898_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_inc_ref(v_value_1990_);
v___x_1998_ = l_Lean_MessageData_ofExpr(v_value_1990_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1965_, v___x_1999_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref_known(v___x_2000_, 1);
v___y_1906_ = v___x_1983_;
v___y_1907_ = v_a_1985_;
v___y_1908_ = v___y_1968_;
v___y_1909_ = v___y_1970_;
v___y_1910_ = v___y_1971_;
v___y_1911_ = v___y_1972_;
v___y_1912_ = v___y_1973_;
v___y_1913_ = v___y_1974_;
v___y_1914_ = v___y_1975_;
goto v___jp_1905_;
}
else
{
lean_dec(v_a_1985_);
lean_dec_ref(v___y_1968_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec_ref(v_docCtx_1855_);
return v___x_2000_;
}
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___y_1968_);
lean_del_object(v___x_1903_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_del_object(v___x_1898_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec_ref(v_docCtx_1855_);
v_a_2003_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1984_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1984_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
v___jp_2011_:
{
if (lean_obj_tag(v_termMeasures_x3f_1868_) == 1)
{
lean_object* v_val_2021_; 
lean_dec_ref(v___y_2014_);
v_val_2021_ = lean_ctor_get(v_termMeasures_x3f_1868_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v_termMeasures_x3f_1868_, 1);
v___y_1967_ = v___y_2012_;
v___y_1968_ = v___y_2013_;
v_wf_1969_ = v_val_2021_;
v___y_1970_ = v___y_2015_;
v___y_1971_ = v___y_2016_;
v___y_1972_ = v___y_2017_;
v___y_1973_ = v___y_2018_;
v___y_1974_ = v___y_2019_;
v___y_1975_ = v___y_2020_;
goto v___jp_1966_;
}
else
{
uint8_t v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_termMeasures_x3f_1868_);
v___x_2022_ = 1;
v___x_2023_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_2014_, v___x_2022_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___y_1967_ = v___y_2012_;
v___y_1968_ = v___y_2013_;
v_wf_1969_ = v_a_2024_;
v___y_1970_ = v___y_2015_;
v___y_1971_ = v___y_2016_;
v___y_1972_ = v___y_2017_;
v___y_1973_ = v___y_2018_;
v___y_1974_ = v___y_2019_;
v___y_1975_ = v___y_2020_;
goto v___jp_1966_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_del_object(v___x_1903_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_del_object(v___x_1898_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec_ref(v_docCtx_1855_);
v_a_2025_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2023_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2023_);
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
v___jp_2033_:
{
lean_object* v___x_2040_; lean_object* v_env_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2040_ = lean_st_ref_get(v___y_2039_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc_ref(v_env_2041_);
lean_dec(v___x_2040_);
v___x_2042_ = l_Lean_Environment_unlockAsync(v_env_2041_);
v___x_2043_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_2042_, v___f_1964_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2062_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v_fst_2045_ = lean_ctor_get(v_a_2044_, 0);
v_snd_2046_ = lean_ctor_get(v_a_2044_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_a_2044_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2048_ = v_a_2044_;
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snd_2046_);
lean_inc(v_fst_2045_);
lean_dec(v_a_2044_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v_a_2052_; uint8_t v___x_2053_; 
lean_inc(v_fst_1900_);
lean_inc(v_fst_1896_);
lean_inc(v_fst_2045_);
lean_inc(v_a_1871_);
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2050_, 0, v_a_1871_);
lean_closure_set(v___f_2050_, 1, v_fst_2045_);
lean_closure_set(v___f_2050_, 2, v_fst_1896_);
lean_closure_set(v___f_2050_, 3, v_fst_1900_);
v___x_2051_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1965_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = lean_unbox(v_a_2052_);
lean_dec(v_a_2052_);
if (v___x_2053_ == 0)
{
lean_del_object(v___x_2048_);
v___y_2012_ = v_fst_2045_;
v___y_2013_ = v_snd_2046_;
v___y_2014_ = v___f_2050_;
v___y_2015_ = v___y_2034_;
v___y_2016_ = v___y_2035_;
v___y_2017_ = v___y_2036_;
v___y_2018_ = v___y_2037_;
v___y_2019_ = v___y_2038_;
v___y_2020_ = v___y_2039_;
goto v___jp_2011_;
}
else
{
lean_object* v_value_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v_value_2054_ = lean_ctor_get(v_snd_1901_, 7);
v___x_2055_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2054_);
v___x_2056_ = l_Lean_MessageData_ofExpr(v_value_2054_);
v___x_2057_ = l_Lean_indentD(v___x_2056_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 7);
lean_ctor_set(v___x_2048_, 1, v___x_2057_);
lean_ctor_set(v___x_2048_, 0, v___x_2055_);
v___x_2059_ = v___x_2048_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1965_, v___x_2059_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_dec_ref_known(v___x_2060_, 1);
v___y_2012_ = v_fst_2045_;
v___y_2013_ = v_snd_2046_;
v___y_2014_ = v___f_2050_;
v___y_2015_ = v___y_2034_;
v___y_2016_ = v___y_2035_;
v___y_2017_ = v___y_2036_;
v___y_2018_ = v___y_2037_;
v___y_2019_ = v___y_2038_;
v___y_2020_ = v___y_2039_;
goto v___jp_2011_;
}
else
{
lean_dec_ref(v___f_2050_);
lean_dec(v_snd_2046_);
lean_dec(v_fst_2045_);
lean_del_object(v___x_1903_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_del_object(v___x_1898_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec(v_termMeasures_x3f_1868_);
lean_dec_ref(v_docCtx_1855_);
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_1903_);
lean_dec(v_snd_1901_);
lean_dec(v_fst_1900_);
lean_del_object(v___x_1898_);
lean_dec(v_fst_1896_);
lean_dec(v_a_1871_);
lean_dec(v_termMeasures_x3f_1868_);
lean_dec_ref(v_docCtx_1855_);
v_a_2063_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2043_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2043_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_1871_);
lean_dec(v_termMeasures_x3f_1868_);
lean_dec_ref(v_docCtx_1855_);
v_a_2082_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_1893_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_1893_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
v___jp_1873_:
{
size_t v_sz_1882_; lean_object* v___x_1883_; 
v_sz_1882_ = lean_array_size(v___y_1874_);
lean_inc(v___y_1875_);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1875_, v___y_1874_, v_sz_1882_, v___x_1867_, v___x_1872_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1883_, 1);
v___x_1884_ = l_Lean_enableRealizationsForConst(v___y_1875_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref_known(v___x_1884_, 1);
v___x_1885_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1874_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1885_;
}
else
{
lean_dec_ref(v___y_1874_);
return v___x_1884_;
}
}
else
{
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_termMeasures_x3f_1868_);
lean_dec_ref(v_docCtx_1855_);
v_a_2090_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_1870_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_1870_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_wfRecursion_0interp(lean_interpreter_value* stack)
{
lean_object* v_docCtx_1855_ = stack[0].m_obj;
lean_object* v_preDefs_1856_ = stack[1].m_obj;
lean_object* v_termMeasure_x3fs_1857_ = stack[2].m_obj;
lean_object* v_a_1858_ = stack[3].m_obj;
lean_object* v_a_1859_ = stack[4].m_obj;
lean_object* v_a_1860_ = stack[5].m_obj;
lean_object* v_a_1861_ = stack[6].m_obj;
lean_object* v_a_1862_ = stack[7].m_obj;
lean_object* v_a_1863_ = stack[8].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l_Lean_Elab_wfRecursion(v_docCtx_1855_, v_preDefs_1856_, v_termMeasure_x3fs_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2099_, lean_object* v_preDefs_2100_, lean_object* v_termMeasure_x3fs_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Elab_wfRecursion(v_docCtx_2099_, v_preDefs_2100_, v_termMeasure_x3fs_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
return v_res_2109_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2110_, lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2111_ = stack[1].m_obj;
lean_object* v___y_2112_ = stack[2].m_obj;
lean_object* v___y_2113_ = stack[3].m_obj;
lean_object* v___y_2114_ = stack[4].m_obj;
lean_object* v___y_2115_ = stack[5].m_obj;
lean_object* v___y_2116_ = stack[6].m_obj;
lean_object* v___y_2117_ = stack[7].m_obj;
lean_object* v_res_2120_;
v_res_2120_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_box(0), v_msg_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
stack->m_obj
 = v_res_2120_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2121_, v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2130_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t v_sz_2131_, size_t v_i_2132_, lean_object* v_bs_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_2131_, v_i_2132_, v_bs_2133_, v___y_2138_, v___y_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2131_ = stack[0].m_num;
size_t v_i_2132_ = stack[1].m_num;
lean_object* v_bs_2133_ = stack[2].m_obj;
lean_object* v___y_2134_ = stack[3].m_obj;
lean_object* v___y_2135_ = stack[4].m_obj;
lean_object* v___y_2136_ = stack[5].m_obj;
lean_object* v___y_2137_ = stack[6].m_obj;
lean_object* v___y_2138_ = stack[7].m_obj;
lean_object* v___y_2139_ = stack[8].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_2131_, v_i_2132_, v_bs_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_sz_2143_, lean_object* v_i_2144_, lean_object* v_bs_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
size_t v_sz_boxed_2153_; size_t v_i_boxed_2154_; lean_object* v_res_2155_; 
v_sz_boxed_2153_ = lean_unbox_usize(v_sz_2143_);
lean_dec(v_sz_2143_);
v_i_boxed_2154_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_boxed_2153_, v_i_boxed_2154_, v_bs_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2155_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_as_2156_, size_t v_sz_2157_, size_t v_i_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_2156_, v_sz_2157_, v_i_2158_, v_b_2159_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2156_ = stack[0].m_obj;
size_t v_sz_2157_ = stack[1].m_num;
size_t v_i_2158_ = stack[2].m_num;
lean_object* v_b_2159_ = stack[3].m_obj;
lean_object* v___y_2160_ = stack[4].m_obj;
lean_object* v___y_2161_ = stack[5].m_obj;
lean_object* v___y_2162_ = stack[6].m_obj;
lean_object* v___y_2163_ = stack[7].m_obj;
lean_object* v___y_2164_ = stack[8].m_obj;
lean_object* v___y_2165_ = stack[9].m_obj;
lean_object* v_res_2168_;
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2156_, v_sz_2157_, v_i_2158_, v_b_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
stack->m_obj
 = v_res_2168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_as_2169_, lean_object* v_sz_2170_, lean_object* v_i_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2170_);
lean_dec(v_sz_2170_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2171_);
lean_dec(v_i_2171_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2169_, v_sz_boxed_2180_, v_i_boxed_2181_, v_b_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_as_2169_);
return v_res_2182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_a_2183_, lean_object* v_as_2184_, size_t v_sz_2185_, size_t v_i_2186_, lean_object* v_bs_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_2183_, v_sz_2185_, v_i_2186_, v_bs_2187_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2183_ = stack[0].m_obj;
lean_object* v_as_2184_ = stack[1].m_obj;
size_t v_sz_2185_ = stack[2].m_num;
size_t v_i_2186_ = stack[3].m_num;
lean_object* v_bs_2187_ = stack[4].m_obj;
lean_object* v___y_2188_ = stack[5].m_obj;
lean_object* v___y_2189_ = stack[6].m_obj;
lean_object* v___y_2190_ = stack[7].m_obj;
lean_object* v___y_2191_ = stack[8].m_obj;
lean_object* v___y_2192_ = stack[9].m_obj;
lean_object* v___y_2193_ = stack[10].m_obj;
lean_object* v_res_2196_;
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2183_, v_as_2184_, v_sz_2185_, v_i_2186_, v_bs_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
stack->m_obj
 = v_res_2196_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_a_2197_, lean_object* v_as_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
size_t v_sz_boxed_2209_; size_t v_i_boxed_2210_; lean_object* v_res_2211_; 
v_sz_boxed_2209_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2210_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2197_, v_as_2198_, v_sz_boxed_2209_, v_i_boxed_2210_, v_bs_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_as_2198_);
return v_res_2211_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_a_2212_, lean_object* v___x_2213_, size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_bs_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_2212_, v___x_2213_, v_sz_2214_, v_i_2215_, v_bs_2216_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2212_ = stack[0].m_obj;
lean_object* v___x_2213_ = stack[1].m_obj;
size_t v_sz_2214_ = stack[2].m_num;
size_t v_i_2215_ = stack[3].m_num;
lean_object* v_bs_2216_ = stack[4].m_obj;
lean_object* v___y_2217_ = stack[5].m_obj;
lean_object* v___y_2218_ = stack[6].m_obj;
lean_object* v___y_2219_ = stack[7].m_obj;
lean_object* v___y_2220_ = stack[8].m_obj;
lean_object* v___y_2221_ = stack[9].m_obj;
lean_object* v___y_2222_ = stack[10].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2212_, v___x_2213_, v_sz_2214_, v_i_2215_, v_bs_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_a_2226_, lean_object* v___x_2227_, lean_object* v_sz_2228_, lean_object* v_i_2229_, lean_object* v_bs_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2226_, v___x_2227_, v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2240_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_00_u03b1_2241_, lean_object* v_env_2242_, lean_object* v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_2242_, v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2242_ = stack[1].m_obj;
lean_object* v_x_2243_ = stack[2].m_obj;
lean_object* v___y_2244_ = stack[3].m_obj;
lean_object* v___y_2245_ = stack[4].m_obj;
lean_object* v___y_2246_ = stack[5].m_obj;
lean_object* v___y_2247_ = stack[6].m_obj;
lean_object* v___y_2248_ = stack[7].m_obj;
lean_object* v___y_2249_ = stack[8].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_box(0), v_env_2242_, v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_env_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(v_00_u03b1_2253_, v_env_2254_, v_x_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2263_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2264_, lean_object* v_msg_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2264_, v_msg_2265_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2264_ = stack[0].m_obj;
lean_object* v_msg_2265_ = stack[1].m_obj;
lean_object* v___y_2266_ = stack[2].m_obj;
lean_object* v___y_2267_ = stack[3].m_obj;
lean_object* v___y_2268_ = stack[4].m_obj;
lean_object* v___y_2269_ = stack[5].m_obj;
lean_object* v___y_2270_ = stack[6].m_obj;
lean_object* v___y_2271_ = stack[7].m_obj;
lean_object* v_res_2274_;
v_res_2274_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2264_, v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
stack->m_obj
 = v_res_2274_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2275_, lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2275_, v_msg_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2284_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_bs_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2285_, v_i_2286_, v_bs_2287_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2285_ = stack[0].m_num;
size_t v_i_2286_ = stack[1].m_num;
lean_object* v_bs_2287_ = stack[2].m_obj;
lean_object* v___y_2288_ = stack[3].m_obj;
lean_object* v___y_2289_ = stack[4].m_obj;
lean_object* v___y_2290_ = stack[5].m_obj;
lean_object* v___y_2291_ = stack[6].m_obj;
lean_object* v___y_2292_ = stack[7].m_obj;
lean_object* v___y_2293_ = stack[8].m_obj;
lean_object* v_res_2296_;
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_2285_, v_i_2286_, v_bs_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
stack->m_obj
 = v_res_2296_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_bs_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
size_t v_sz_boxed_2307_; size_t v_i_boxed_2308_; lean_object* v_res_2309_; 
v_sz_boxed_2307_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2308_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2307_, v_i_boxed_2308_, v_bs_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2309_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2310_, lean_object* v_as_2311_, size_t v_sz_2312_, size_t v_i_2313_, lean_object* v_b_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2310_, v_as_2311_, v_sz_2312_, v_i_2313_, v_b_2314_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2310_ = stack[0].m_obj;
lean_object* v_as_2311_ = stack[1].m_obj;
size_t v_sz_2312_ = stack[2].m_num;
size_t v_i_2313_ = stack[3].m_num;
lean_object* v_b_2314_ = stack[4].m_obj;
lean_object* v___y_2315_ = stack[5].m_obj;
lean_object* v___y_2316_ = stack[6].m_obj;
lean_object* v___y_2317_ = stack[7].m_obj;
lean_object* v___y_2318_ = stack[8].m_obj;
lean_object* v___y_2319_ = stack[9].m_obj;
lean_object* v___y_2320_ = stack[10].m_obj;
lean_object* v_res_2323_;
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2310_, v_as_2311_, v_sz_2312_, v_i_2313_, v_b_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
stack->m_obj
 = v_res_2323_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2324_, lean_object* v_as_2325_, lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2324_, v_as_2325_, v_sz_boxed_2336_, v_i_boxed_2337_, v_b_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_as_2325_);
return v_res_2338_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2339_, lean_object* v_x_2340_, uint8_t v_isExporting_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2340_, v_isExporting_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2340_ = stack[1].m_obj;
uint8_t v_isExporting_2341_ = stack[2].m_num;
lean_object* v___y_2342_ = stack[3].m_obj;
lean_object* v___y_2343_ = stack[4].m_obj;
lean_object* v___y_2344_ = stack[5].m_obj;
lean_object* v___y_2345_ = stack[6].m_obj;
lean_object* v___y_2346_ = stack[7].m_obj;
lean_object* v___y_2347_ = stack[8].m_obj;
lean_object* v_res_2350_;
v_res_2350_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_box(0), v_x_2340_, v_isExporting_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
stack->m_obj
 = v_res_2350_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2351_, lean_object* v_x_2352_, lean_object* v_isExporting_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v_isExporting_boxed_2361_; lean_object* v_res_2362_; 
v_isExporting_boxed_2361_ = lean_unbox(v_isExporting_2353_);
v_res_2362_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2351_, v_x_2352_, v_isExporting_boxed_2361_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2362_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2363_, lean_object* v_x_2364_, uint8_t v_when_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2364_, v_when_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2364_ = stack[1].m_obj;
uint8_t v_when_2365_ = stack[2].m_num;
lean_object* v___y_2366_ = stack[3].m_obj;
lean_object* v___y_2367_ = stack[4].m_obj;
lean_object* v___y_2368_ = stack[5].m_obj;
lean_object* v___y_2369_ = stack[6].m_obj;
lean_object* v___y_2370_ = stack[7].m_obj;
lean_object* v___y_2371_ = stack[8].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_box(0), v_x_2364_, v_when_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_x_2376_, lean_object* v_when_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v_when_boxed_2385_; lean_object* v_res_2386_; 
v_when_boxed_2385_ = lean_unbox(v_when_2377_);
v_res_2386_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2375_, v_x_2376_, v_when_boxed_2385_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2386_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2387_, lean_object* v_macroStack_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2387_, v_macroStack_2388_, v___y_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2387_ = stack[0].m_obj;
lean_object* v_macroStack_2388_ = stack[1].m_obj;
lean_object* v___y_2389_ = stack[2].m_obj;
lean_object* v___y_2390_ = stack[3].m_obj;
lean_object* v___y_2391_ = stack[4].m_obj;
lean_object* v___y_2392_ = stack[5].m_obj;
lean_object* v___y_2393_ = stack[6].m_obj;
lean_object* v___y_2394_ = stack[7].m_obj;
lean_object* v_res_2397_;
v_res_2397_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2387_, v_macroStack_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
stack->m_obj
 = v_res_2397_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2398_, lean_object* v_macroStack_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2398_, v_macroStack_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2407_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2408_, lean_object* v_msgData_2409_, uint8_t v_severity_2410_, uint8_t v_isSilent_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2408_, v_msgData_2409_, v_severity_2410_, v_isSilent_2411_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2408_ = stack[0].m_obj;
lean_object* v_msgData_2409_ = stack[1].m_obj;
uint8_t v_severity_2410_ = stack[2].m_num;
uint8_t v_isSilent_2411_ = stack[3].m_num;
lean_object* v___y_2412_ = stack[4].m_obj;
lean_object* v___y_2413_ = stack[5].m_obj;
lean_object* v___y_2414_ = stack[6].m_obj;
lean_object* v___y_2415_ = stack[7].m_obj;
lean_object* v___y_2416_ = stack[8].m_obj;
lean_object* v___y_2417_ = stack[9].m_obj;
lean_object* v_res_2420_;
v_res_2420_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2408_, v_msgData_2409_, v_severity_2410_, v_isSilent_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2421_, lean_object* v_msgData_2422_, lean_object* v_severity_2423_, lean_object* v_isSilent_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v_severity_boxed_2432_; uint8_t v_isSilent_boxed_2433_; lean_object* v_res_2434_; 
v_severity_boxed_2432_ = lean_unbox(v_severity_2423_);
v_isSilent_boxed_2433_ = lean_unbox(v_isSilent_2424_);
v_res_2434_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2421_, v_msgData_2422_, v_severity_boxed_2432_, v_isSilent_boxed_2433_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v_ref_2421_);
return v_res_2434_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2506_ = 0;
v___x_2507_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2508_ = l_Lean_registerTraceClass(v___x_2505_, v___x_2506_, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2509_;
v_res_2509_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2511_;
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
