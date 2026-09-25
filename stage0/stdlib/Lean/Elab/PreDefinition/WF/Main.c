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
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v_toCold_320_; lean_object* v_mctx_321_; lean_object* v_lctx_322_; lean_object* v_options_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = lean_st_ref_get(v___y_313_);
v_toCold_320_ = lean_ctor_get(v___y_314_, 0);
v_mctx_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_mctx_321_);
lean_dec(v___x_319_);
v_lctx_322_ = lean_ctor_get(v___y_312_, 2);
v_options_323_ = lean_ctor_get(v_toCold_320_, 2);
lean_inc_ref(v_options_323_);
lean_inc_ref(v_lctx_322_);
v___x_324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_324_, 0, v_env_318_);
lean_ctor_set(v___x_324_, 1, v_mctx_321_);
lean_ctor_set(v___x_324_, 2, v_lctx_322_);
lean_ctor_set(v___x_324_, 3, v_options_323_);
v___x_325_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_msgData_311_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_ref_342_; lean_object* v_macroStack_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_ref_342_ = lean_ctor_get(v___y_339_, 2);
v_macroStack_343_ = lean_ctor_get(v___y_335_, 1);
v___x_344_ = l_Lean_Elab_getBetterRef(v_ref_342_, v_macroStack_343_);
v___x_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_334_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
lean_inc(v_macroStack_343_);
v___x_347_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_346_, v_macroStack_343_, v___y_339_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_344_);
lean_ctor_set(v___x_352_, 1, v_a_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object* v_as_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_a_384_; uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_b_375_);
return v___x_389_;
}
else
{
lean_object* v_array_390_; lean_object* v_start_391_; lean_object* v_stop_392_; uint8_t v___x_393_; 
v_array_390_ = lean_ctor_get(v_b_375_, 0);
v_start_391_ = lean_ctor_get(v_b_375_, 1);
v_stop_392_ = lean_ctor_get(v_b_375_, 2);
v___x_393_ = lean_nat_dec_lt(v_start_391_, v_stop_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v_b_375_);
return v___x_394_;
}
else
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_423_; 
lean_inc(v_stop_392_);
lean_inc(v_start_391_);
lean_inc_ref(v_array_390_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_b_375_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_424_ = lean_ctor_get(v_b_375_, 2);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_b_375_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_b_375_, 0);
lean_dec(v_unused_426_);
v___x_396_ = v_b_375_;
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_b_375_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_a_398_ = lean_array_uget_borrowed(v_as_372_, v_i_374_);
v___x_399_ = lean_array_fget(v_array_390_, v_start_391_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_start_391_, v___x_400_);
lean_dec(v_start_391_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_401_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_array_390_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_stop_392_);
v___x_403_ = v_reuseFailAlloc_422_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_array_get_size(v_a_398_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_nat_dec_eq(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v___x_399_);
v_a_384_ = v___x_403_;
goto v___jp_383_;
}
else
{
lean_object* v_declName_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_declName_407_ = lean_ctor_get(v___x_399_, 3);
lean_inc(v_declName_407_);
lean_dec(v___x_399_);
v___x_408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1);
v___x_409_ = l_Lean_MessageData_ofName(v_declName_407_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_412_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref_known(v___x_413_, 1);
v_a_384_ = v___x_403_;
goto v___jp_383_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v___x_403_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
}
}
v___jp_383_:
{
size_t v___x_385_; size_t v___x_386_; 
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_374_, v___x_385_);
v_i_374_ = v___x_386_;
v_b_375_ = v_a_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_as_427_, lean_object* v_sz_428_, lean_object* v_i_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
size_t v_sz_boxed_438_; size_t v_i_boxed_439_; lean_object* v_res_440_; 
v_sz_boxed_438_ = lean_unbox_usize(v_sz_428_);
lean_dec(v_sz_428_);
v_i_boxed_439_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_427_, v_sz_boxed_438_, v_i_boxed_439_, v_b_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_as_427_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t v_sz_441_, size_t v_i_442_, lean_object* v_bs_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_444_ == 0)
{
return v_bs_443_;
}
else
{
lean_object* v_v_445_; lean_object* v_declName_446_; lean_object* v___x_447_; lean_object* v_bs_x27_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_445_ = lean_array_uget_borrowed(v_bs_443_, v_i_442_);
v_declName_446_ = lean_ctor_get(v_v_445_, 3);
lean_inc(v_declName_446_);
v___x_447_ = lean_unsigned_to_nat(0u);
v_bs_x27_448_ = lean_array_uset(v_bs_443_, v_i_442_, v___x_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_442_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_448_, v_i_442_, v_declName_446_);
v_i_442_ = v___x_450_;
v_bs_443_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_boxed_456_, v_i_boxed_457_, v_bs_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_a_459_, lean_object* v___x_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_bs_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v___x_460_);
lean_dec_ref(v_a_459_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_bs_463_);
return v___x_468_;
}
else
{
lean_object* v_v_469_; lean_object* v_ref_470_; uint8_t v_kind_471_; lean_object* v_levelParams_472_; lean_object* v_modifiers_473_; lean_object* v_declName_474_; lean_object* v_binders_475_; lean_object* v_numSectionVars_476_; lean_object* v_type_477_; lean_object* v_value_478_; lean_object* v_termination_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_505_; 
v_v_469_ = lean_array_uget(v_bs_463_, v_i_462_);
v_ref_470_ = lean_ctor_get(v_v_469_, 0);
v_kind_471_ = lean_ctor_get_uint8(v_v_469_, sizeof(void*)*9);
v_levelParams_472_ = lean_ctor_get(v_v_469_, 1);
v_modifiers_473_ = lean_ctor_get(v_v_469_, 2);
v_declName_474_ = lean_ctor_get(v_v_469_, 3);
v_binders_475_ = lean_ctor_get(v_v_469_, 4);
v_numSectionVars_476_ = lean_ctor_get(v_v_469_, 5);
v_type_477_ = lean_ctor_get(v_v_469_, 6);
v_value_478_ = lean_ctor_get(v_v_469_, 7);
v_termination_479_ = lean_ctor_get(v_v_469_, 8);
v_isSharedCheck_505_ = !lean_is_exclusive(v_v_469_);
if (v_isSharedCheck_505_ == 0)
{
v___x_481_ = v_v_469_;
v_isShared_482_ = v_isSharedCheck_505_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_termination_479_);
lean_inc(v_value_478_);
lean_inc(v_type_477_);
lean_inc(v_numSectionVars_476_);
lean_inc(v_binders_475_);
lean_inc(v_declName_474_);
lean_inc(v_modifiers_473_);
lean_inc(v_levelParams_472_);
lean_inc(v_ref_470_);
lean_dec(v_v_469_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_505_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
size_t v_sz_483_; lean_object* v___x_484_; lean_object* v_bs_x27_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_sz_483_ = lean_array_size(v_a_459_);
v___x_484_ = lean_unsigned_to_nat(0u);
v_bs_x27_485_ = lean_array_uset(v_bs_463_, v_i_462_, v___x_484_);
v___x_486_ = ((size_t)0ULL);
lean_inc_ref(v_a_459_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_483_, v___x_486_, v_a_459_);
lean_inc(v___x_460_);
v___x_488_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_487_, v___x_460_, v_value_478_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 7, v_a_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_ref_470_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_levelParams_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_modifiers_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_declName_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_binders_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_numSectionVars_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_type_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_a_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_termination_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*9, v_kind_471_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_462_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_485_, v_i_462_, v___x_491_);
v_i_462_ = v___x_493_;
v_bs_463_ = v___x_494_;
goto _start;
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_bs_x27_485_);
lean_del_object(v___x_481_);
lean_dec_ref(v_termination_479_);
lean_dec_ref(v_type_477_);
lean_dec(v_numSectionVars_476_);
lean_dec(v_binders_475_);
lean_dec(v_declName_474_);
lean_dec_ref(v_modifiers_473_);
lean_dec(v_levelParams_472_);
lean_dec(v_ref_470_);
lean_dec(v___x_460_);
lean_dec_ref(v_a_459_);
v_a_497_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_488_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_a_506_, lean_object* v___x_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_515_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_506_, v___x_507_, v_sz_boxed_514_, v_i_boxed_515_, v_bs_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_517_, size_t v_sz_518_, size_t v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_517_, v_sz_518_, v___x_519_, v___x_520_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; 
lean_dec_ref_known(v___x_529_, 1);
lean_inc_ref(v_a_517_);
v___x_530_ = l_Lean_Elab_getFixedParamPerms(v_a_517_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_n(v_a_531_, 2);
lean_dec_ref_known(v___x_530_, 1);
lean_inc_ref(v_a_517_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_531_, v_sz_518_, v___x_519_, v_a_517_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; size_t v_sz_537_; lean_object* v___x_538_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_a_517_);
lean_inc_ref(v_a_517_);
v___x_536_ = l_Array_toSubarray___redArg(v_a_517_, v___x_534_, v___x_535_);
v_sz_537_ = lean_array_size(v_a_533_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_a_533_, v_sz_537_, v___x_519_, v___x_536_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v_numSectionVars_540_; lean_object* v___x_541_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_539_ = lean_array_get_borrowed(v___x_521_, v_a_517_, v___x_534_);
v_numSectionVars_540_ = lean_ctor_get(v___x_539_, 5);
lean_inc(v_numSectionVars_540_);
lean_inc_ref(v_a_517_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_517_, v_numSectionVars_540_, v_sz_518_, v___x_519_, v_a_517_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
lean_inc(v_a_533_);
lean_inc(v_a_531_);
v___x_543_ = l_Lean_Elab_WF_packMutual(v_a_531_, v_a_533_, v_a_542_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_a_533_);
lean_ctor_set(v___x_548_, 1, v_a_544_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_531_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
v_a_554_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_543_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_543_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
v_a_562_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_541_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_541_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_517_);
v_a_570_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_538_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_538_);
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
lean_dec(v_a_531_);
lean_dec_ref(v_a_517_);
v_a_578_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_532_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_532_);
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
lean_dec_ref(v_a_517_);
v_a_586_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_530_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_530_);
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
lean_dec_ref(v_a_517_);
v_a_594_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_529_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_529_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_602_, lean_object* v_sz_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
size_t v_sz_boxed_614_; size_t v___x_43996__boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v___x_43996__boxed_615_ = lean_unbox_usize(v___x_604_);
lean_dec(v___x_604_);
v_res_616_ = l_Lean_Elab_wfRecursion___lam__0(v_a_602_, v_sz_boxed_614_, v___x_43996__boxed_615_, v___x_605_, v___x_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec_ref(v___x_606_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_617_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_ref_626_; uint8_t v_kind_627_; lean_object* v_levelParams_628_; lean_object* v_modifiers_629_; lean_object* v_declName_630_; lean_object* v_binders_631_; lean_object* v_numSectionVars_632_; lean_object* v_type_633_; lean_object* v_value_634_; lean_object* v_termination_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref_known(v___x_625_, 1);
v_ref_626_ = lean_ctor_get(v_snd_617_, 0);
v_kind_627_ = lean_ctor_get_uint8(v_snd_617_, sizeof(void*)*9);
v_levelParams_628_ = lean_ctor_get(v_snd_617_, 1);
v_modifiers_629_ = lean_ctor_get(v_snd_617_, 2);
v_declName_630_ = lean_ctor_get(v_snd_617_, 3);
v_binders_631_ = lean_ctor_get(v_snd_617_, 4);
v_numSectionVars_632_ = lean_ctor_get(v_snd_617_, 5);
v_type_633_ = lean_ctor_get(v_snd_617_, 6);
v_value_634_ = lean_ctor_get(v_snd_617_, 7);
v_termination_635_ = lean_ctor_get(v_snd_617_, 8);
v_isSharedCheck_661_ = !lean_is_exclusive(v_snd_617_);
if (v_isSharedCheck_661_ == 0)
{
v___x_637_ = v_snd_617_;
v_isShared_638_ = v_isSharedCheck_661_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_termination_635_);
lean_inc(v_value_634_);
lean_inc(v_type_633_);
lean_inc(v_numSectionVars_632_);
lean_inc(v_binders_631_);
lean_inc(v_declName_630_);
lean_inc(v_modifiers_629_);
lean_inc(v_levelParams_628_);
lean_inc(v_ref_626_);
lean_dec(v_snd_617_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_661_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Elab_WF_preprocess(v_value_634_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_expr_644_; lean_object* v___x_646_; 
v_expr_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_expr_644_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 7, v_expr_644_);
v___x_646_ = v___x_637_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_ref_626_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_levelParams_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_modifiers_629_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_declName_630_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_binders_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 5, v_numSectionVars_632_);
lean_ctor_set(v_reuseFailAlloc_651_, 6, v_type_633_);
lean_ctor_set(v_reuseFailAlloc_651_, 7, v_expr_644_);
lean_ctor_set(v_reuseFailAlloc_651_, 8, v_termination_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_651_, sizeof(void*)*9, v_kind_627_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_637_);
lean_dec_ref(v_termination_635_);
lean_dec_ref(v_type_633_);
lean_dec(v_numSectionVars_632_);
lean_dec(v_binders_631_);
lean_dec(v_declName_630_);
lean_dec_ref(v_modifiers_629_);
lean_dec(v_levelParams_628_);
lean_dec(v_ref_626_);
v_a_653_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_639_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_639_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_snd_617_);
v_a_662_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_625_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_625_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_toCold_690_; lean_object* v_options_691_; uint8_t v_hasTrace_692_; 
v_toCold_690_ = lean_ctor_get(v___y_687_, 0);
v_options_691_ = lean_ctor_get(v_toCold_690_, 2);
v_hasTrace_692_ = lean_ctor_get_uint8(v_options_691_, sizeof(void*)*1);
if (v_hasTrace_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_682_);
v___x_693_ = lean_box(v_hasTrace_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v_inheritedTraceOptions_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_inheritedTraceOptions_695_ = lean_ctor_get(v_toCold_690_, 11);
v___x_696_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
v___x_697_ = l_Lean_Name_append(v___x_696_, v___x_682_);
v___x_698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_695_, v_options_691_, v___x_697_);
lean_dec(v___x_697_);
v___x_699_ = lean_box(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v___x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_wfRecursion___lam__2(v___x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_717_, uint8_t v___y_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_719_) == 1)
{
lean_object* v_pre_720_; 
v_pre_720_ = lean_ctor_get(v_x_719_, 0);
switch(lean_obj_tag(v_pre_720_))
{
case 1:
{
lean_object* v_pre_721_; 
v_pre_721_ = lean_ctor_get(v_pre_720_, 0);
switch(lean_obj_tag(v_pre_721_))
{
case 0:
{
lean_object* v_str_722_; lean_object* v_str_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_str_722_ = lean_ctor_get(v_x_719_, 1);
v_str_723_ = lean_ctor_get(v_pre_720_, 1);
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_725_ = lean_string_dec_eq(v_str_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_727_ = lean_string_dec_eq(v_str_723_, v___x_726_);
if (v___x_727_ == 0)
{
return v___x_727_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_729_ = lean_string_dec_eq(v_str_722_, v___x_728_);
if (v___x_729_ == 0)
{
return v___x_729_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_731_ = lean_string_dec_eq(v_str_722_, v___x_730_);
if (v___x_731_ == 0)
{
return v___x_731_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
case 1:
{
lean_object* v_pre_732_; 
v_pre_732_ = lean_ctor_get(v_pre_721_, 0);
if (lean_obj_tag(v_pre_732_) == 0)
{
lean_object* v_str_733_; lean_object* v_str_734_; lean_object* v_str_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_str_733_ = lean_ctor_get(v_x_719_, 1);
v_str_734_ = lean_ctor_get(v_pre_720_, 1);
v_str_735_ = lean_ctor_get(v_pre_721_, 1);
v___x_736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_737_ = lean_string_dec_eq(v_str_735_, v___x_736_);
if (v___x_737_ == 0)
{
return v___x_737_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_739_ = lean_string_dec_eq(v_str_734_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_741_ = lean_string_dec_eq(v_str_733_, v___x_740_);
if (v___x_741_ == 0)
{
return v___x_741_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
}
else
{
return v___y_718_;
}
}
default: 
{
return v___y_718_;
}
}
}
case 0:
{
lean_object* v_str_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_str_742_ = lean_ctor_get(v_x_719_, 1);
v___x_743_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_744_ = lean_string_dec_eq(v_str_742_, v___x_743_);
if (v___x_744_ == 0)
{
return v___x_744_;
}
else
{
return v_suppressElabErrors_717_;
}
}
default: 
{
return v___y_718_;
}
}
}
else
{
return v___y_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_745_, lean_object* v___y_746_, lean_object* v_x_747_){
_start:
{
uint8_t v_suppressElabErrors_boxed_748_; uint8_t v___y_44326__boxed_749_; uint8_t v_res_750_; lean_object* v_r_751_; 
v_suppressElabErrors_boxed_748_ = lean_unbox(v_suppressElabErrors_745_);
v___y_44326__boxed_749_ = lean_unbox(v___y_746_);
v_res_750_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_748_, v___y_44326__boxed_749_, v_x_747_);
lean_dec(v_x_747_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_753_, lean_object* v_msgData_754_, uint8_t v_severity_755_, uint8_t v_isSilent_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_toCold_770_; lean_object* v___y_771_; lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; uint8_t v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_837_; uint8_t v___y_838_; uint8_t v___y_839_; uint8_t v___x_850_; uint8_t v___y_852_; uint8_t v___y_853_; uint8_t v___y_854_; uint8_t v___y_856_; uint8_t v___x_864_; 
v___x_850_ = 2;
v___x_864_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_850_);
if (v___x_864_ == 0)
{
v___y_856_ = v___x_864_;
goto v___jp_855_;
}
else
{
uint8_t v___x_865_; 
lean_inc_ref(v_msgData_754_);
v___x_865_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_754_);
v___y_856_ = v___x_865_;
goto v___jp_855_;
}
v___jp_762_:
{
lean_object* v_currNamespace_772_; lean_object* v_openDecls_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_env_778_; lean_object* v_nextMacroScope_779_; lean_object* v_ngen_780_; lean_object* v_auxDeclNGen_781_; lean_object* v_traceState_782_; lean_object* v_cache_783_; lean_object* v_recordedDeps_784_; lean_object* v_messages_785_; lean_object* v_infoState_786_; lean_object* v_snapshotTasks_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_798_; 
v_currNamespace_772_ = lean_ctor_get(v_toCold_770_, 4);
v_openDecls_773_ = lean_ctor_get(v_toCold_770_, 5);
lean_inc(v_openDecls_773_);
lean_inc(v_currNamespace_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_currNamespace_772_);
lean_ctor_set(v___x_774_, 1, v_openDecls_773_);
v___x_775_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___y_765_);
lean_inc_ref(v___y_768_);
lean_inc_ref(v___y_767_);
v___x_776_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_776_, 0, v___y_767_);
lean_ctor_set(v___x_776_, 1, v___y_764_);
lean_ctor_set(v___x_776_, 2, v___y_769_);
lean_ctor_set(v___x_776_, 3, v___y_768_);
lean_ctor_set(v___x_776_, 4, v___x_775_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*5, v___y_766_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*5 + 1, v___y_763_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*5 + 2, v_isSilent_756_);
v___x_777_ = lean_st_ref_take(v___y_771_);
v_env_778_ = lean_ctor_get(v___x_777_, 0);
v_nextMacroScope_779_ = lean_ctor_get(v___x_777_, 1);
v_ngen_780_ = lean_ctor_get(v___x_777_, 2);
v_auxDeclNGen_781_ = lean_ctor_get(v___x_777_, 3);
v_traceState_782_ = lean_ctor_get(v___x_777_, 4);
v_cache_783_ = lean_ctor_get(v___x_777_, 5);
v_recordedDeps_784_ = lean_ctor_get(v___x_777_, 6);
v_messages_785_ = lean_ctor_get(v___x_777_, 7);
v_infoState_786_ = lean_ctor_get(v___x_777_, 8);
v_snapshotTasks_787_ = lean_ctor_get(v___x_777_, 9);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_798_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snapshotTasks_787_);
lean_inc(v_infoState_786_);
lean_inc(v_messages_785_);
lean_inc(v_recordedDeps_784_);
lean_inc(v_cache_783_);
lean_inc(v_traceState_782_);
lean_inc(v_auxDeclNGen_781_);
lean_inc(v_ngen_780_);
lean_inc(v_nextMacroScope_779_);
lean_inc(v_env_778_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_box(0);
v___x_792_ = l_Lean_MessageLog_add(v___x_776_, v_messages_785_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 7, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_env_778_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_nextMacroScope_779_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_ngen_780_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_auxDeclNGen_781_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_traceState_782_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_cache_783_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v_recordedDeps_784_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_infoState_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 9, v_snapshotTasks_787_);
v___x_794_ = v_reuseFailAlloc_797_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_st_ref_put(v___y_771_, v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_791_);
return v___x_796_;
}
}
}
v___jp_799_:
{
lean_object* v_fileName_808_; lean_object* v_fileMap_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_825_; 
v_fileName_808_ = lean_ctor_get(v___y_806_, 0);
v_fileMap_809_ = lean_ctor_get(v___y_806_, 1);
v___x_810_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_754_);
v___x_811_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_810_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_825_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_825_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_825_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_inc_ref_n(v_fileMap_809_, 2);
v___x_816_ = l_Lean_FileMap_toPosition(v_fileMap_809_, v___y_803_);
lean_dec(v___y_803_);
v___x_817_ = l_Lean_FileMap_toPosition(v_fileMap_809_, v___y_807_);
lean_dec(v___y_807_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_805_ == 0)
{
lean_del_object(v___x_814_);
lean_dec_ref(v___y_800_);
v___y_763_ = v___y_802_;
v___y_764_ = v___x_816_;
v___y_765_ = v_a_812_;
v___y_766_ = v___y_804_;
v___y_767_ = v_fileName_808_;
v___y_768_ = v___x_819_;
v___y_769_ = v___x_818_;
v_toCold_770_ = v___y_801_;
v___y_771_ = v___y_760_;
goto v___jp_762_;
}
else
{
uint8_t v___x_820_; 
lean_inc(v_a_812_);
v___x_820_ = l_Lean_MessageData_hasTag(v___y_800_, v_a_812_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec_ref_known(v___x_818_, 1);
lean_dec_ref(v___x_816_);
lean_dec(v_a_812_);
v___x_821_ = lean_box(0);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_821_);
v___x_823_ = v___x_814_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_del_object(v___x_814_);
v___y_763_ = v___y_802_;
v___y_764_ = v___x_816_;
v___y_765_ = v_a_812_;
v___y_766_ = v___y_804_;
v___y_767_ = v_fileName_808_;
v___y_768_ = v___x_819_;
v___y_769_ = v___x_818_;
v_toCold_770_ = v___y_801_;
v___y_771_ = v___y_760_;
goto v___jp_762_;
}
}
}
}
v___jp_826_:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_Syntax_getTailPos_x3f(v___y_832_, v___y_831_);
lean_dec(v___y_832_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_inc(v___y_833_);
v___y_800_ = v___y_827_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_833_;
v___y_804_ = v___y_831_;
v___y_805_ = v___y_829_;
v___y_806_ = v___y_828_;
v___y_807_ = v___y_833_;
goto v___jp_799_;
}
else
{
lean_object* v_val_835_; 
v_val_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v___x_834_, 1);
v___y_800_ = v___y_827_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_833_;
v___y_804_ = v___y_831_;
v___y_805_ = v___y_829_;
v___y_806_ = v___y_828_;
v___y_807_ = v_val_835_;
goto v___jp_799_;
}
}
v___jp_836_:
{
lean_object* v_toCold_840_; lean_object* v_ref_841_; uint8_t v_suppressElabErrors_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v_ref_846_; lean_object* v___x_847_; 
v_toCold_840_ = lean_ctor_get(v___y_759_, 0);
v_ref_841_ = lean_ctor_get(v___y_759_, 2);
v_suppressElabErrors_842_ = lean_ctor_get_uint8(v___y_759_, sizeof(void*)*3 + 2);
v___x_843_ = lean_box(v_suppressElabErrors_842_);
v___x_844_ = lean_box(v___y_837_);
v___f_845_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_845_, 0, v___x_843_);
lean_closure_set(v___f_845_, 1, v___x_844_);
v_ref_846_ = l_Lean_replaceRef(v_ref_753_, v_ref_841_);
v___x_847_ = l_Lean_Syntax_getPos_x3f(v_ref_846_, v___y_838_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___y_827_ = v___f_845_;
v___y_828_ = v_toCold_840_;
v___y_829_ = v_suppressElabErrors_842_;
v___y_830_ = v___y_839_;
v___y_831_ = v___y_838_;
v___y_832_ = v_ref_846_;
v___y_833_ = v___x_848_;
goto v___jp_826_;
}
else
{
lean_object* v_val_849_; 
v_val_849_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___x_847_, 1);
v___y_827_ = v___f_845_;
v___y_828_ = v_toCold_840_;
v___y_829_ = v_suppressElabErrors_842_;
v___y_830_ = v___y_839_;
v___y_831_ = v___y_838_;
v___y_832_ = v_ref_846_;
v___y_833_ = v_val_849_;
goto v___jp_826_;
}
}
v___jp_851_:
{
if (v___y_854_ == 0)
{
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v_severity_755_;
goto v___jp_836_;
}
else
{
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___x_850_;
goto v___jp_836_;
}
}
v___jp_855_:
{
if (v___y_856_ == 0)
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 1;
v___x_858_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_852_ = v___y_856_;
v___y_853_ = v___y_856_;
v___y_854_ = v___x_858_;
goto v___jp_851_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_759_);
v___x_860_ = l_Lean_warningAsError;
v___x_861_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v___x_859_, v___x_860_);
lean_dec_ref(v___x_859_);
v___y_852_ = v___y_856_;
v___y_853_ = v___y_856_;
v___y_854_ = v___x_861_;
goto v___jp_851_;
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v_msgData_754_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_866_, lean_object* v_msgData_867_, lean_object* v_severity_868_, lean_object* v_isSilent_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_severity_boxed_875_; uint8_t v_isSilent_boxed_876_; lean_object* v_res_877_; 
v_severity_boxed_875_ = lean_unbox(v_severity_868_);
v_isSilent_boxed_876_ = lean_unbox(v_isSilent_869_);
v_res_877_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_866_, v_msgData_867_, v_severity_boxed_875_, v_isSilent_boxed_876_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v_ref_866_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_878_, lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = 1;
v___x_888_ = 0;
v___x_889_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_878_, v_msgData_879_, v___x_887_, v___x_888_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_890_, lean_object* v_msgData_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_890_, v_msgData_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v_ref_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_908_, lean_object* v_as_909_, size_t v_i_910_, size_t v_stop_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_a_921_; uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_910_, v_stop_911_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v_name_927_; lean_object* v_stx_928_; uint8_t v___y_930_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_926_ = lean_array_uget_borrowed(v_as_909_, v_i_910_);
v_name_927_ = lean_ctor_get(v___x_926_, 0);
v_stx_928_ = lean_ctor_get(v___x_926_, 1);
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_941_ = lean_name_eq(v_name_927_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_943_ = lean_name_eq(v_name_927_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_box(0);
v_a_921_ = v___x_944_;
goto v___jp_920_;
}
else
{
v___y_930_ = v___x_943_;
goto v___jp_929_;
}
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_nat_dec_lt(v___x_945_, v___x_908_);
v___y_930_ = v___x_946_;
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_927_);
v___x_932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_927_, v___y_930_);
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
v___x_936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___x_937_ = l_Lean_MessageData_ofFormat(v___x_936_);
v___x_938_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_928_, v___x_937_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v_a_921_ = v_a_939_;
goto v___jp_920_;
}
else
{
return v___x_938_;
}
}
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_912_);
return v___x_947_;
}
v___jp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_910_, v___x_922_);
v_i_910_ = v___x_923_;
v_b_912_ = v_a_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_948_, lean_object* v_as_949_, lean_object* v_i_950_, lean_object* v_stop_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_951_);
lean_dec(v_stop_951_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_948_, v_as_949_, v_i_boxed_960_, v_stop_boxed_961_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
lean_dec(v___x_948_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_963_, lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_a_976_; lean_object* v___y_981_; uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v_modifiers_985_; lean_object* v_attrs_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_984_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
v_modifiers_985_ = lean_ctor_get(v___x_984_, 2);
v_attrs_986_ = lean_ctor_get(v_modifiers_985_, 2);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_array_get_size(v_attrs_986_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
if (v___x_990_ == 0)
{
v_a_976_ = v___x_989_;
goto v___jp_975_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = lean_nat_dec_le(v___x_988_, v___x_988_);
if (v___x_991_ == 0)
{
if (v___x_990_ == 0)
{
v_a_976_ = v___x_989_;
goto v___jp_975_;
}
else
{
size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_992_ = ((size_t)0ULL);
v___x_993_ = lean_usize_of_nat(v___x_988_);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_963_, v_attrs_986_, v___x_992_, v___x_993_, v___x_989_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
v___y_981_ = v___x_994_;
goto v___jp_980_;
}
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((size_t)0ULL);
v___x_996_ = lean_usize_of_nat(v___x_988_);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_963_, v_attrs_986_, v___x_995_, v___x_996_, v___x_989_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
v___y_981_ = v___x_997_;
goto v___jp_980_;
}
}
}
else
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_b_967_);
return v___x_998_;
}
v___jp_975_:
{
size_t v___x_977_; size_t v___x_978_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_965_, v___x_977_);
v_i_965_ = v___x_978_;
v_b_967_ = v_a_976_;
goto _start;
}
v___jp_980_:
{
if (lean_obj_tag(v___y_981_) == 0)
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v___y_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___y_981_, 1);
v_a_976_ = v_a_982_;
goto v___jp_975_;
}
else
{
return v___y_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_999_, lean_object* v_as_1000_, lean_object* v_i_1001_, lean_object* v_stop_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_i_boxed_1011_; size_t v_stop_boxed_1012_; lean_object* v_res_1013_; 
v_i_boxed_1011_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_stop_boxed_1012_ = lean_unbox_usize(v_stop_1002_);
lean_dec(v_stop_1002_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_999_, v_as_1000_, v_i_boxed_1011_, v_stop_boxed_1012_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_as_1000_);
lean_dec(v___x_999_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_bs_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1017_ == 0)
{
return v_bs_1016_;
}
else
{
lean_object* v_v_1018_; lean_object* v_termination_1019_; lean_object* v_decreasingBy_x3f_1020_; lean_object* v___x_1021_; lean_object* v_bs_x27_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v_v_1018_ = lean_array_uget_borrowed(v_bs_1016_, v_i_1015_);
v_termination_1019_ = lean_ctor_get(v_v_1018_, 8);
v_decreasingBy_x3f_1020_ = lean_ctor_get(v_termination_1019_, 4);
lean_inc(v_decreasingBy_x3f_1020_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v_bs_x27_1022_ = lean_array_uset(v_bs_1016_, v_i_1015_, v___x_1021_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1015_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1022_, v_i_1015_, v_decreasingBy_x3f_1020_);
v_i_1015_ = v___x_1024_;
v_bs_1016_ = v___x_1025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1030_, v_i_boxed_1031_, v_bs_1029_);
return v_res_1032_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1033_; double v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_float_of_nat(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_ref_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1091_; 
v_ref_1044_ = lean_ctor_get(v___y_1041_, 2);
v___x_1045_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1091_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1091_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v_traceState_1051_; lean_object* v_env_1052_; lean_object* v_nextMacroScope_1053_; lean_object* v_ngen_1054_; lean_object* v_auxDeclNGen_1055_; lean_object* v_cache_1056_; lean_object* v_recordedDeps_1057_; lean_object* v_messages_1058_; lean_object* v_infoState_1059_; lean_object* v_snapshotTasks_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1090_; 
v___x_1050_ = lean_st_ref_take(v___y_1042_);
v_traceState_1051_ = lean_ctor_get(v___x_1050_, 4);
v_env_1052_ = lean_ctor_get(v___x_1050_, 0);
v_nextMacroScope_1053_ = lean_ctor_get(v___x_1050_, 1);
v_ngen_1054_ = lean_ctor_get(v___x_1050_, 2);
v_auxDeclNGen_1055_ = lean_ctor_get(v___x_1050_, 3);
v_cache_1056_ = lean_ctor_get(v___x_1050_, 5);
v_recordedDeps_1057_ = lean_ctor_get(v___x_1050_, 6);
v_messages_1058_ = lean_ctor_get(v___x_1050_, 7);
v_infoState_1059_ = lean_ctor_get(v___x_1050_, 8);
v_snapshotTasks_1060_ = lean_ctor_get(v___x_1050_, 9);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1062_ = v___x_1050_;
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_snapshotTasks_1060_);
lean_inc(v_infoState_1059_);
lean_inc(v_messages_1058_);
lean_inc(v_recordedDeps_1057_);
lean_inc(v_cache_1056_);
lean_inc(v_traceState_1051_);
lean_inc(v_auxDeclNGen_1055_);
lean_inc(v_ngen_1054_);
lean_inc(v_nextMacroScope_1053_);
lean_inc(v_env_1052_);
lean_dec(v___x_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1090_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint64_t v_tid_1064_; lean_object* v_traces_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1089_; 
v_tid_1064_ = lean_ctor_get_uint64(v_traceState_1051_, sizeof(void*)*1);
v_traces_1065_ = lean_ctor_get(v_traceState_1051_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_traceState_1051_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1067_ = v_traceState_1051_;
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_traces_1065_);
lean_dec(v_traceState_1051_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1089_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; double v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1072_ = 0;
v___x_1073_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1074_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1074_, 0, v_cls_1037_);
lean_ctor_set(v___x_1074_, 1, v___x_1070_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
lean_ctor_set_float(v___x_1074_, sizeof(void*)*3, v___x_1071_);
lean_ctor_set_float(v___x_1074_, sizeof(void*)*3 + 8, v___x_1071_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3 + 16, v___x_1072_);
v___x_1075_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1076_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v_a_1046_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
lean_inc(v_ref_1044_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_ref_1044_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_PersistentArray_push___redArg(v_traces_1065_, v___x_1077_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1078_);
v___x_1080_ = v___x_1067_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1078_);
lean_ctor_set_uint64(v_reuseFailAlloc_1088_, sizeof(void*)*1, v_tid_1064_);
v___x_1080_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1080_);
v___x_1082_ = v___x_1062_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_env_1052_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_nextMacroScope_1053_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_ngen_1054_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_auxDeclNGen_1055_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1087_, 5, v_cache_1056_);
lean_ctor_set(v_reuseFailAlloc_1087_, 6, v_recordedDeps_1057_);
lean_ctor_set(v_reuseFailAlloc_1087_, 7, v_messages_1058_);
lean_ctor_set(v_reuseFailAlloc_1087_, 8, v_infoState_1059_);
lean_ctor_set(v_reuseFailAlloc_1087_, 9, v_snapshotTasks_1060_);
v___x_1082_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_st_ref_put(v___y_1042_, v___x_1082_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1069_);
v___x_1085_ = v___x_1048_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1069_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1103_, lean_object* v_snd_1104_, size_t v_sz_1105_, size_t v___x_1106_, lean_object* v_a_1107_, lean_object* v_fixedArgs_1108_, lean_object* v_fst_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v_wfRel_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v_a_1129_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_toCold_1279_; lean_object* v_options_1280_; uint8_t v_hasTrace_1281_; 
v_toCold_1279_ = lean_ctor_get(v___y_1118_, 0);
v_options_1280_ = lean_ctor_get(v_toCold_1279_, 2);
v_hasTrace_1281_ = lean_ctor_get_uint8(v_options_1280_, sizeof(void*)*1);
if (v_hasTrace_1281_ == 0)
{
lean_dec(v___x_1112_);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v_inheritedTraceOptions_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_inheritedTraceOptions_1282_ = lean_ctor_get(v_toCold_1279_, 11);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
lean_inc(v___x_1112_);
v___x_1284_ = l_Lean_Name_append(v___x_1283_, v___x_1112_);
v___x_1285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1282_, v_options_1280_, v___x_1284_);
lean_dec(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1112_);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1113_);
v___x_1287_ = l_Lean_MessageData_ofExpr(v_wfRel_1113_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1112_, v___x_1288_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
v___y_1255_ = v___y_1114_;
v___y_1256_ = v___y_1115_;
v___y_1257_ = v___y_1116_;
v___y_1258_ = v___y_1117_;
v___y_1259_ = v___y_1118_;
v___y_1260_ = v___y_1119_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
v___jp_1121_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v___x_1130_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1124_, v___y_1122_, v___y_1127_);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1138_);
v___x_1132_ = v___x_1130_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
lean_ctor_set(v___x_1132_, 0, v_a_1129_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
v___jp_1139_:
{
if (lean_obj_tag(v___y_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v_env_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_a_1148_ = lean_ctor_get(v___y_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___y_1147_, 1);
v___x_1149_ = lean_st_ref_get(v___y_1145_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref_n(v_env_1150_, 2);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1142_, v___y_1140_, v___y_1145_);
lean_dec_ref(v___x_1151_);
v___x_1152_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1150_, v_a_1148_, v___y_1146_, v___y_1145_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1213_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1213_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1213_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v_env_1158_; lean_object* v_nextMacroScope_1159_; lean_object* v_ngen_1160_; lean_object* v_auxDeclNGen_1161_; lean_object* v_traceState_1162_; lean_object* v_recordedDeps_1163_; lean_object* v_messages_1164_; lean_object* v_infoState_1165_; lean_object* v_snapshotTasks_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1211_; 
v___x_1157_ = lean_st_ref_take(v___y_1145_);
v_env_1158_ = lean_ctor_get(v___x_1157_, 0);
v_nextMacroScope_1159_ = lean_ctor_get(v___x_1157_, 1);
v_ngen_1160_ = lean_ctor_get(v___x_1157_, 2);
v_auxDeclNGen_1161_ = lean_ctor_get(v___x_1157_, 3);
v_traceState_1162_ = lean_ctor_get(v___x_1157_, 4);
v_recordedDeps_1163_ = lean_ctor_get(v___x_1157_, 6);
v_messages_1164_ = lean_ctor_get(v___x_1157_, 7);
v_infoState_1165_ = lean_ctor_get(v___x_1157_, 8);
v_snapshotTasks_1166_ = lean_ctor_get(v___x_1157_, 9);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1157_, 5);
lean_dec(v_unused_1212_);
v___x_1168_ = v___x_1157_;
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snapshotTasks_1166_);
lean_inc(v_infoState_1165_);
lean_inc(v_messages_1164_);
lean_inc(v_recordedDeps_1163_);
lean_inc(v_traceState_1162_);
lean_inc(v_auxDeclNGen_1161_);
lean_inc(v_ngen_1160_);
lean_inc(v_nextMacroScope_1159_);
lean_inc(v_env_1158_);
lean_dec(v___x_1157_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1211_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_copyExtraModUses(v_env_1150_, v_env_1158_);
v___x_1171_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 5, v___x_1171_);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_nextMacroScope_1159_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_ngen_1160_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_auxDeclNGen_1161_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_traceState_1162_);
lean_ctor_set(v_reuseFailAlloc_1210_, 5, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1210_, 6, v_recordedDeps_1163_);
lean_ctor_set(v_reuseFailAlloc_1210_, 7, v_messages_1164_);
lean_ctor_set(v_reuseFailAlloc_1210_, 8, v_infoState_1165_);
lean_ctor_set(v_reuseFailAlloc_1210_, 9, v_snapshotTasks_1166_);
v___x_1173_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_mctx_1176_; lean_object* v_zetaDeltaFVarIds_1177_; lean_object* v_postponed_1178_; lean_object* v_diag_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1208_; 
v___x_1174_ = lean_st_ref_put(v___y_1145_, v___x_1173_);
v___x_1175_ = lean_st_ref_take(v___y_1140_);
v_mctx_1176_ = lean_ctor_get(v___x_1175_, 0);
v_zetaDeltaFVarIds_1177_ = lean_ctor_get(v___x_1175_, 2);
v_postponed_1178_ = lean_ctor_get(v___x_1175_, 3);
v_diag_1179_ = lean_ctor_get(v___x_1175_, 4);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1175_, 1);
lean_dec(v_unused_1209_);
v___x_1181_ = v___x_1175_;
v_isShared_1182_ = v_isSharedCheck_1208_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_diag_1179_);
lean_inc(v_postponed_1178_);
lean_inc(v_zetaDeltaFVarIds_1177_);
lean_inc(v_mctx_1176_);
lean_dec(v___x_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1208_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_mctx_1176_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_zetaDeltaFVarIds_1177_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_postponed_1178_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_diag_1179_);
v___x_1185_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v_ref_1187_; uint8_t v_kind_1188_; lean_object* v_levelParams_1189_; lean_object* v_modifiers_1190_; lean_object* v_declName_1191_; lean_object* v_binders_1192_; lean_object* v_numSectionVars_1193_; lean_object* v_type_1194_; lean_object* v_termination_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v___x_1186_ = lean_st_ref_put(v___y_1140_, v___x_1185_);
v_ref_1187_ = lean_ctor_get(v_fst_1103_, 0);
v_kind_1188_ = lean_ctor_get_uint8(v_fst_1103_, sizeof(void*)*9);
v_levelParams_1189_ = lean_ctor_get(v_fst_1103_, 1);
v_modifiers_1190_ = lean_ctor_get(v_fst_1103_, 2);
v_declName_1191_ = lean_ctor_get(v_fst_1103_, 3);
v_binders_1192_ = lean_ctor_get(v_fst_1103_, 4);
v_numSectionVars_1193_ = lean_ctor_get(v_fst_1103_, 5);
v_type_1194_ = lean_ctor_get(v_fst_1103_, 6);
v_termination_1195_ = lean_ctor_get(v_fst_1103_, 8);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_fst_1103_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_fst_1103_, 7);
lean_dec(v_unused_1206_);
v___x_1197_ = v_fst_1103_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_termination_1195_);
lean_inc(v_type_1194_);
lean_inc(v_numSectionVars_1193_);
lean_inc(v_binders_1192_);
lean_inc(v_declName_1191_);
lean_inc(v_modifiers_1190_);
lean_inc(v_levelParams_1189_);
lean_inc(v_ref_1187_);
lean_dec(v_fst_1103_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 7, v_a_1153_);
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_ref_1187_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_levelParams_1189_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_modifiers_1190_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_declName_1191_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_binders_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 5, v_numSectionVars_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 6, v_type_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_a_1153_);
lean_ctor_set(v_reuseFailAlloc_1204_, 8, v_termination_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*9, v_kind_1188_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1200_);
v___x_1202_ = v___x_1155_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
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
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_env_1150_);
lean_dec_ref(v_fst_1103_);
v_a_1214_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1152_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1152_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; 
lean_dec_ref(v_fst_1103_);
v_a_1222_ = lean_ctor_get(v___y_1147_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___y_1147_, 1);
v___y_1122_ = v___y_1140_;
v___y_1123_ = v___y_1141_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1146_;
v_a_1129_ = v_a_1222_;
goto v___jp_1121_;
}
}
v___jp_1223_:
{
lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_st_ref_get(v___y_1229_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1104_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref_known(v___x_1232_, 1);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1105_, v___x_1106_, v_a_1107_);
lean_inc_ref(v_fst_1103_);
v___x_1234_ = l_Lean_Elab_WF_mkFix(v_fst_1103_, v_fixedArgs_1108_, v_fst_1109_, v_wfRel_1113_, v___x_1110_, v___x_1233_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1235_, v___y_1228_, v___y_1229_);
v___y_1140_ = v___y_1227_;
v___y_1141_ = v___y_1226_;
v___y_1142_ = v_env_1231_;
v___y_1143_ = v___y_1225_;
v___y_1144_ = v___y_1224_;
v___y_1145_ = v___y_1229_;
v___y_1146_ = v___y_1228_;
v___y_1147_ = v___x_1236_;
goto v___jp_1139_;
}
else
{
v___y_1140_ = v___y_1227_;
v___y_1141_ = v___y_1226_;
v___y_1142_ = v_env_1231_;
v___y_1143_ = v___y_1225_;
v___y_1144_ = v___y_1224_;
v___y_1145_ = v___y_1229_;
v___y_1146_ = v___y_1228_;
v___y_1147_ = v___x_1234_;
goto v___jp_1139_;
}
}
else
{
lean_object* v_a_1237_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1237_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1232_, 1);
v___y_1122_ = v___y_1227_;
v___y_1123_ = v___y_1226_;
v___y_1124_ = v_env_1231_;
v___y_1125_ = v___y_1225_;
v___y_1126_ = v___y_1224_;
v___y_1127_ = v___y_1229_;
v___y_1128_ = v___y_1228_;
v_a_1129_ = v_a_1237_;
goto v___jp_1121_;
}
}
v___jp_1238_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_dec_ref_known(v___y_1245_, 1);
v___y_1224_ = v___y_1240_;
v___y_1225_ = v___y_1239_;
v___y_1226_ = v___y_1242_;
v___y_1227_ = v___y_1243_;
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1241_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1246_ = lean_ctor_get(v___y_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___y_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___y_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___y_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
v___jp_1254_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v_wfRel_1113_);
v___x_1261_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1113_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_a_1107_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1266_ == 0)
{
if (v___x_1265_ == 0)
{
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
else
{
size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_usize_of_nat(v___x_1264_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1264_, v_a_1107_, v___x_1106_, v___x_1267_, v___x_1111_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1255_;
v___y_1241_ = v___y_1260_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1258_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___x_1268_;
goto v___jp_1238_;
}
}
else
{
size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_usize_of_nat(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1264_, v_a_1107_, v___x_1106_, v___x_1269_, v___x_1111_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1255_;
v___y_1241_ = v___y_1260_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1258_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___x_1270_;
goto v___jp_1238_;
}
}
}
else
{
lean_dec_ref_known(v_a_1262_, 1);
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
v___y_1227_ = v___y_1258_;
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
goto v___jp_1223_;
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_wfRel_1113_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_fst_1109_);
lean_dec_ref(v_fixedArgs_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_fst_1103_);
v_a_1271_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1261_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1298_ = _args[0];
lean_object* v_snd_1299_ = _args[1];
lean_object* v_sz_1300_ = _args[2];
lean_object* v___x_1301_ = _args[3];
lean_object* v_a_1302_ = _args[4];
lean_object* v_fixedArgs_1303_ = _args[5];
lean_object* v_fst_1304_ = _args[6];
lean_object* v___x_1305_ = _args[7];
lean_object* v___x_1306_ = _args[8];
lean_object* v___x_1307_ = _args[9];
lean_object* v_wfRel_1308_ = _args[10];
lean_object* v___y_1309_ = _args[11];
lean_object* v___y_1310_ = _args[12];
lean_object* v___y_1311_ = _args[13];
lean_object* v___y_1312_ = _args[14];
lean_object* v___y_1313_ = _args[15];
lean_object* v___y_1314_ = _args[16];
lean_object* v___y_1315_ = _args[17];
_start:
{
size_t v_sz_boxed_1316_; size_t v___x_44917__boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v___x_44917__boxed_1317_ = lean_unbox_usize(v___x_1301_);
lean_dec(v___x_1301_);
v_res_1318_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1298_, v_snd_1299_, v_sz_boxed_1316_, v___x_44917__boxed_1317_, v_a_1302_, v_fixedArgs_1303_, v_fst_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v_wfRel_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_snd_1299_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1322_, size_t v___x_1323_, lean_object* v_a_1324_, lean_object* v_fst_1325_, lean_object* v_snd_1326_, lean_object* v_fst_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v_declName_1330_, lean_object* v_fst_1331_, lean_object* v_wf_1332_, lean_object* v_fixedArgs_1333_, lean_object* v_type_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_whnfForall(v_type_1334_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___x_1357_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1357_ = l_Lean_Expr_isForall(v_a_1343_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v_fst_1327_);
lean_dec_ref(v_snd_1326_);
lean_dec_ref(v_fst_1325_);
lean_dec_ref(v_a_1324_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1359_ = l_Lean_MessageData_ofExpr(v_a_1343_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1360_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
v___y_1345_ = v___y_1335_;
v___y_1346_ = v___y_1336_;
v___y_1347_ = v___y_1337_;
v___y_1348_ = v___y_1338_;
v___y_1349_ = v___y_1339_;
v___y_1350_ = v___y_1340_;
goto v___jp_1344_;
}
v___jp_1344_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; 
v___x_1351_ = l_Lean_Expr_bindingDomain_x21(v_a_1343_);
lean_dec(v_a_1343_);
lean_inc_ref(v_a_1324_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_1322_, v___x_1323_, v_a_1324_);
v___x_1353_ = lean_box_usize(v_sz_1322_);
v___x_1354_ = lean_box_usize(v___x_1323_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v_fst_1327_);
lean_inc_ref(v_fixedArgs_1333_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1355_, 0, v_fst_1325_);
lean_closure_set(v___f_1355_, 1, v_snd_1326_);
lean_closure_set(v___f_1355_, 2, v___x_1353_);
lean_closure_set(v___f_1355_, 3, v___x_1354_);
lean_closure_set(v___f_1355_, 4, v_a_1324_);
lean_closure_set(v___f_1355_, 5, v_fixedArgs_1333_);
lean_closure_set(v___f_1355_, 6, v_fst_1327_);
lean_closure_set(v___f_1355_, 7, v___x_1352_);
lean_closure_set(v___f_1355_, 8, v___x_1328_);
lean_closure_set(v___f_1355_, 9, v___x_1329_);
v___x_1356_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1352_, v_declName_1330_, v_fst_1331_, v_fixedArgs_1333_, v_fst_1327_, v___x_1351_, v_wf_1332_, v___f_1355_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1356_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v_fst_1327_);
lean_dec_ref(v_snd_1326_);
lean_dec_ref(v_fst_1325_);
lean_dec_ref(v_a_1324_);
v_a_1370_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1342_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1342_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1378_ = _args[0];
lean_object* v___x_1379_ = _args[1];
lean_object* v_a_1380_ = _args[2];
lean_object* v_fst_1381_ = _args[3];
lean_object* v_snd_1382_ = _args[4];
lean_object* v_fst_1383_ = _args[5];
lean_object* v___x_1384_ = _args[6];
lean_object* v___x_1385_ = _args[7];
lean_object* v_declName_1386_ = _args[8];
lean_object* v_fst_1387_ = _args[9];
lean_object* v_wf_1388_ = _args[10];
lean_object* v_fixedArgs_1389_ = _args[11];
lean_object* v_type_1390_ = _args[12];
lean_object* v___y_1391_ = _args[13];
lean_object* v___y_1392_ = _args[14];
lean_object* v___y_1393_ = _args[15];
lean_object* v___y_1394_ = _args[16];
lean_object* v___y_1395_ = _args[17];
lean_object* v___y_1396_ = _args[18];
lean_object* v___y_1397_ = _args[19];
_start:
{
size_t v_sz_boxed_1398_; size_t v___x_45276__boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v___x_45276__boxed_1399_ = lean_unbox_usize(v___x_1379_);
lean_dec(v___x_1379_);
v_res_1400_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1398_, v___x_45276__boxed_1399_, v_a_1380_, v_fst_1381_, v_snd_1382_, v_fst_1383_, v___x_1384_, v___x_1385_, v_declName_1386_, v_fst_1387_, v_wf_1388_, v_fixedArgs_1389_, v_type_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1401_, lean_object* v_fst_1402_, lean_object* v_fst_1403_, lean_object* v_fst_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Elab_WF_guessLex(v_a_1401_, v_fst_1402_, v_fst_1403_, v_fst_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1413_, lean_object* v_fst_1414_, lean_object* v_fst_1415_, lean_object* v_fst_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1413_, v_fst_1414_, v_fst_1415_, v_fst_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_env_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_env_1435_; lean_object* v_a_1437_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1434_ = lean_st_ref_get(v___y_1432_);
v_env_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_ref(v_env_1435_);
lean_dec(v___x_1434_);
v___x_1447_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1425_, v___y_1430_, v___y_1432_);
lean_dec_ref(v___x_1447_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
v___x_1448_ = lean_apply_7(v_x_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, lean_box(0));
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1435_, v___y_1430_, v___y_1432_);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1450_, 0);
lean_dec(v_unused_1458_);
v___x_1452_ = v___x_1450_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1450_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_a_1449_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1449_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1448_, 1);
v_a_1437_ = v_a_1459_;
goto v___jp_1436_;
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v___x_1438_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1435_, v___y_1430_, v___y_1432_);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1446_);
v___x_1440_ = v___x_1438_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v___x_1438_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v_a_1437_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1437_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_env_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1460_, v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1470_, uint8_t v_isExporting_1471_, lean_object* v___x_1472_, lean_object* v___y_1473_, lean_object* v___x_1474_, lean_object* v_a_x3f_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v_env_1478_; lean_object* v_nextMacroScope_1479_; lean_object* v_ngen_1480_; lean_object* v_auxDeclNGen_1481_; lean_object* v_traceState_1482_; lean_object* v_recordedDeps_1483_; lean_object* v_messages_1484_; lean_object* v_infoState_1485_; lean_object* v_snapshotTasks_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1511_; 
v___x_1477_ = lean_st_ref_take(v___y_1470_);
v_env_1478_ = lean_ctor_get(v___x_1477_, 0);
v_nextMacroScope_1479_ = lean_ctor_get(v___x_1477_, 1);
v_ngen_1480_ = lean_ctor_get(v___x_1477_, 2);
v_auxDeclNGen_1481_ = lean_ctor_get(v___x_1477_, 3);
v_traceState_1482_ = lean_ctor_get(v___x_1477_, 4);
v_recordedDeps_1483_ = lean_ctor_get(v___x_1477_, 6);
v_messages_1484_ = lean_ctor_get(v___x_1477_, 7);
v_infoState_1485_ = lean_ctor_get(v___x_1477_, 8);
v_snapshotTasks_1486_ = lean_ctor_get(v___x_1477_, 9);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v___x_1477_, 5);
lean_dec(v_unused_1512_);
v___x_1488_ = v___x_1477_;
v_isShared_1489_ = v_isSharedCheck_1511_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snapshotTasks_1486_);
lean_inc(v_infoState_1485_);
lean_inc(v_messages_1484_);
lean_inc(v_recordedDeps_1483_);
lean_inc(v_traceState_1482_);
lean_inc(v_auxDeclNGen_1481_);
lean_inc(v_ngen_1480_);
lean_inc(v_nextMacroScope_1479_);
lean_inc(v_env_1478_);
lean_dec(v___x_1477_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1511_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = l_Lean_Environment_setExporting(v_env_1478_, v_isExporting_1471_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 5, v___x_1472_);
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_nextMacroScope_1479_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_ngen_1480_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_auxDeclNGen_1481_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_traceState_1482_);
lean_ctor_set(v_reuseFailAlloc_1510_, 5, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1510_, 6, v_recordedDeps_1483_);
lean_ctor_set(v_reuseFailAlloc_1510_, 7, v_messages_1484_);
lean_ctor_set(v_reuseFailAlloc_1510_, 8, v_infoState_1485_);
lean_ctor_set(v_reuseFailAlloc_1510_, 9, v_snapshotTasks_1486_);
v___x_1492_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_mctx_1495_; lean_object* v_zetaDeltaFVarIds_1496_; lean_object* v_postponed_1497_; lean_object* v_diag_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1508_; 
v___x_1493_ = lean_st_ref_put(v___y_1470_, v___x_1492_);
v___x_1494_ = lean_st_ref_take(v___y_1473_);
v_mctx_1495_ = lean_ctor_get(v___x_1494_, 0);
v_zetaDeltaFVarIds_1496_ = lean_ctor_get(v___x_1494_, 2);
v_postponed_1497_ = lean_ctor_get(v___x_1494_, 3);
v_diag_1498_ = lean_ctor_get(v___x_1494_, 4);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1494_, 1);
lean_dec(v_unused_1509_);
v___x_1500_ = v___x_1494_;
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_diag_1498_);
lean_inc(v_postponed_1497_);
lean_inc(v_zetaDeltaFVarIds_1496_);
lean_inc(v_mctx_1495_);
lean_dec(v___x_1494_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_box(0);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1474_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_mctx_1495_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_zetaDeltaFVarIds_1496_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_postponed_1497_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_diag_1498_);
v___x_1504_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_st_ref_put(v___y_1473_, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1502_);
return v___x_1506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1513_, lean_object* v_isExporting_1514_, lean_object* v___x_1515_, lean_object* v___y_1516_, lean_object* v___x_1517_, lean_object* v_a_x3f_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_isExporting_boxed_1520_; lean_object* v_res_1521_; 
v_isExporting_boxed_1520_ = lean_unbox(v_isExporting_1514_);
v_res_1521_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1513_, v_isExporting_boxed_1520_, v___x_1515_, v___y_1516_, v___x_1517_, v_a_x3f_1518_);
lean_dec(v_a_x3f_1518_);
lean_dec(v___y_1516_);
lean_dec(v___y_1513_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1522_, uint8_t v_isExporting_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; lean_object* v_env_1532_; lean_object* v___x_1533_; uint8_t v_isModule_1534_; 
v___x_1531_ = lean_st_ref_get(v___y_1529_);
v_env_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_ref(v_env_1532_);
lean_dec(v___x_1531_);
v___x_1533_ = l_Lean_Environment_header(v_env_1532_);
v_isModule_1534_ = lean_ctor_get_uint8(v___x_1533_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1533_);
if (v_isModule_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref(v_env_1532_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v___x_1535_ = lean_apply_7(v_x_1522_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, lean_box(0));
return v___x_1535_;
}
else
{
uint8_t v_isExporting_1536_; 
v_isExporting_1536_ = lean_ctor_get_uint8(v_env_1532_, sizeof(void*)*8);
lean_dec_ref(v_env_1532_);
if (v_isExporting_1523_ == 0)
{
if (v_isExporting_1536_ == 0)
{
lean_object* v___x_1603_; 
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v___x_1603_ = lean_apply_7(v_x_1522_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, lean_box(0));
return v___x_1603_;
}
else
{
goto v___jp_1537_;
}
}
else
{
if (v_isExporting_1536_ == 0)
{
goto v___jp_1537_;
}
else
{
lean_object* v___x_1604_; 
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v___x_1604_ = lean_apply_7(v_x_1522_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, lean_box(0));
return v___x_1604_;
}
}
v___jp_1537_:
{
lean_object* v___x_1538_; lean_object* v_env_1539_; lean_object* v_nextMacroScope_1540_; lean_object* v_ngen_1541_; lean_object* v_auxDeclNGen_1542_; lean_object* v_traceState_1543_; lean_object* v_recordedDeps_1544_; lean_object* v_messages_1545_; lean_object* v_infoState_1546_; lean_object* v_snapshotTasks_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1601_; 
v___x_1538_ = lean_st_ref_take(v___y_1529_);
v_env_1539_ = lean_ctor_get(v___x_1538_, 0);
v_nextMacroScope_1540_ = lean_ctor_get(v___x_1538_, 1);
v_ngen_1541_ = lean_ctor_get(v___x_1538_, 2);
v_auxDeclNGen_1542_ = lean_ctor_get(v___x_1538_, 3);
v_traceState_1543_ = lean_ctor_get(v___x_1538_, 4);
v_recordedDeps_1544_ = lean_ctor_get(v___x_1538_, 6);
v_messages_1545_ = lean_ctor_get(v___x_1538_, 7);
v_infoState_1546_ = lean_ctor_get(v___x_1538_, 8);
v_snapshotTasks_1547_ = lean_ctor_get(v___x_1538_, 9);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1538_, 5);
lean_dec(v_unused_1602_);
v___x_1549_ = v___x_1538_;
v_isShared_1550_ = v_isSharedCheck_1601_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_snapshotTasks_1547_);
lean_inc(v_infoState_1546_);
lean_inc(v_messages_1545_);
lean_inc(v_recordedDeps_1544_);
lean_inc(v_traceState_1543_);
lean_inc(v_auxDeclNGen_1542_);
lean_inc(v_ngen_1541_);
lean_inc(v_nextMacroScope_1540_);
lean_inc(v_env_1539_);
lean_dec(v___x_1538_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1601_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = l_Lean_Environment_setExporting(v_env_1539_, v_isExporting_1523_);
v___x_1552_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 5, v___x_1552_);
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_nextMacroScope_1540_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_ngen_1541_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_auxDeclNGen_1542_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_traceState_1543_);
lean_ctor_set(v_reuseFailAlloc_1600_, 5, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1600_, 6, v_recordedDeps_1544_);
lean_ctor_set(v_reuseFailAlloc_1600_, 7, v_messages_1545_);
lean_ctor_set(v_reuseFailAlloc_1600_, 8, v_infoState_1546_);
lean_ctor_set(v_reuseFailAlloc_1600_, 9, v_snapshotTasks_1547_);
v___x_1554_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_mctx_1557_; lean_object* v_zetaDeltaFVarIds_1558_; lean_object* v_postponed_1559_; lean_object* v_diag_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1598_; 
v___x_1555_ = lean_st_ref_put(v___y_1529_, v___x_1554_);
v___x_1556_ = lean_st_ref_take(v___y_1527_);
v_mctx_1557_ = lean_ctor_get(v___x_1556_, 0);
v_zetaDeltaFVarIds_1558_ = lean_ctor_get(v___x_1556_, 2);
v_postponed_1559_ = lean_ctor_get(v___x_1556_, 3);
v_diag_1560_ = lean_ctor_get(v___x_1556_, 4);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1556_, 1);
lean_dec(v_unused_1599_);
v___x_1562_ = v___x_1556_;
v_isShared_1563_ = v_isSharedCheck_1598_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_diag_1560_);
lean_inc(v_postponed_1559_);
lean_inc(v_zetaDeltaFVarIds_1558_);
lean_inc(v_mctx_1557_);
lean_dec(v___x_1556_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1598_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_mctx_1557_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_zetaDeltaFVarIds_1558_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_postponed_1559_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v_diag_1560_);
v___x_1566_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v_r_1568_; 
v___x_1567_ = lean_st_ref_put(v___y_1527_, v___x_1566_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v_r_1568_ = lean_apply_7(v_x_1522_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, lean_box(0));
if (lean_obj_tag(v_r_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1585_; 
v_a_1569_ = lean_ctor_get(v_r_1568_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_r_1568_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1571_ = v_r_1568_;
v_isShared_1572_ = v_isSharedCheck_1585_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v_r_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1585_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
lean_inc(v_a_1569_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 1);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v___x_1575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1529_, v_isExporting_1536_, v___x_1552_, v___y_1527_, v___x_1564_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1583_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_a_1569_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1569_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1586_ = lean_ctor_get(v_r_1568_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v_r_1568_, 1);
v___x_1587_ = lean_box(0);
v___x_1588_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1529_, v_isExporting_1536_, v___x_1552_, v___y_1527_, v___x_1564_, v___x_1587_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1588_, 0);
lean_dec(v_unused_1596_);
v___x_1590_ = v___x_1588_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v___x_1588_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 1);
lean_ctor_set(v___x_1590_, 0, v_a_1586_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1586_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1605_, lean_object* v_isExporting_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v_isExporting_boxed_1614_; lean_object* v_res_1615_; 
v_isExporting_boxed_1614_ = lean_unbox(v_isExporting_1606_);
v_res_1615_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1605_, v_isExporting_boxed_1614_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1616_, uint8_t v_when_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
if (v_when_1617_ == 0)
{
lean_object* v___x_1625_; 
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
lean_inc(v___y_1621_);
lean_inc_ref(v___y_1620_);
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
v___x_1625_ = lean_apply_7(v_x_1616_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, lean_box(0));
return v___x_1625_;
}
else
{
uint8_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = 0;
v___x_1627_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1616_, v___x_1626_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1628_, lean_object* v_when_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v_when_boxed_1637_; lean_object* v_res_1638_; 
v_when_boxed_1637_ = lean_unbox(v_when_1629_);
v_res_1638_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1628_, v_when_boxed_1637_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t v_sz_1639_, size_t v_i_1640_, lean_object* v_bs_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1640_, v_sz_1639_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_bs_1641_);
return v___x_1646_;
}
else
{
lean_object* v_v_1647_; lean_object* v_ref_1648_; uint8_t v_kind_1649_; lean_object* v_levelParams_1650_; lean_object* v_modifiers_1651_; lean_object* v_declName_1652_; lean_object* v_binders_1653_; lean_object* v_numSectionVars_1654_; lean_object* v_type_1655_; lean_object* v_value_1656_; lean_object* v_termination_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1680_; 
v_v_1647_ = lean_array_uget(v_bs_1641_, v_i_1640_);
v_ref_1648_ = lean_ctor_get(v_v_1647_, 0);
v_kind_1649_ = lean_ctor_get_uint8(v_v_1647_, sizeof(void*)*9);
v_levelParams_1650_ = lean_ctor_get(v_v_1647_, 1);
v_modifiers_1651_ = lean_ctor_get(v_v_1647_, 2);
v_declName_1652_ = lean_ctor_get(v_v_1647_, 3);
v_binders_1653_ = lean_ctor_get(v_v_1647_, 4);
v_numSectionVars_1654_ = lean_ctor_get(v_v_1647_, 5);
v_type_1655_ = lean_ctor_get(v_v_1647_, 6);
v_value_1656_ = lean_ctor_get(v_v_1647_, 7);
v_termination_1657_ = lean_ctor_get(v_v_1647_, 8);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_v_1647_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1659_ = v_v_1647_;
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_termination_1657_);
lean_inc(v_value_1656_);
lean_inc(v_type_1655_);
lean_inc(v_numSectionVars_1654_);
lean_inc(v_binders_1653_);
lean_inc(v_declName_1652_);
lean_inc(v_modifiers_1651_);
lean_inc(v_levelParams_1650_);
lean_inc(v_ref_1648_);
lean_dec(v_v_1647_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v_bs_x27_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v_bs_x27_1662_ = lean_array_uset(v_bs_1641_, v_i_1640_, v___x_1661_);
v___x_1663_ = l_Lean_Elab_WF_floatRecApp(v_value_1656_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 7, v_a_1664_);
v___x_1666_ = v___x_1659_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_ref_1648_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_levelParams_1650_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_modifiers_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_declName_1652_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_binders_1653_);
lean_ctor_set(v_reuseFailAlloc_1671_, 5, v_numSectionVars_1654_);
lean_ctor_set(v_reuseFailAlloc_1671_, 6, v_type_1655_);
lean_ctor_set(v_reuseFailAlloc_1671_, 7, v_a_1664_);
lean_ctor_set(v_reuseFailAlloc_1671_, 8, v_termination_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*9, v_kind_1649_);
v___x_1666_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((size_t)1ULL);
v___x_1668_ = lean_usize_add(v_i_1640_, v___x_1667_);
v___x_1669_ = lean_array_uset(v_bs_x27_1662_, v_i_1640_, v___x_1666_);
v_i_1640_ = v___x_1668_;
v_bs_1641_ = v___x_1669_;
goto _start;
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v_bs_x27_1662_);
lean_del_object(v___x_1659_);
lean_dec_ref(v_termination_1657_);
lean_dec_ref(v_type_1655_);
lean_dec(v_numSectionVars_1654_);
lean_dec(v_binders_1653_);
lean_dec(v_declName_1652_);
lean_dec_ref(v_modifiers_1651_);
lean_dec(v_levelParams_1650_);
lean_dec(v_ref_1648_);
v_a_1672_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1663_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1663_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
size_t v_sz_boxed_1687_; size_t v_i_boxed_1688_; lean_object* v_res_1689_; 
v_sz_boxed_1687_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1688_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_boxed_1687_, v_i_boxed_1688_, v_bs_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_bs_1692_){
_start:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_lt(v_i_1691_, v_sz_1690_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_bs_1692_);
return v___x_1694_;
}
else
{
lean_object* v_v_1695_; 
v_v_1695_ = lean_array_uget_borrowed(v_bs_1692_, v_i_1691_);
if (lean_obj_tag(v_v_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v_bs_1692_);
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1698_; lean_object* v_bs_x27_1699_; size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v_val_1697_ = lean_ctor_get(v_v_1695_, 0);
lean_inc(v_val_1697_);
v___x_1698_ = lean_unsigned_to_nat(0u);
v_bs_x27_1699_ = lean_array_uset(v_bs_1692_, v_i_1691_, v___x_1698_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1691_, v___x_1700_);
v___x_1702_ = lean_array_uset(v_bs_x27_1699_, v_i_1691_, v_val_1697_);
v_i_1691_ = v___x_1701_;
v_bs_1692_ = v___x_1702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_1704_, lean_object* v_i_1705_, lean_object* v_bs_1706_){
_start:
{
size_t v_sz_boxed_1707_; size_t v_i_boxed_1708_; lean_object* v_res_1709_; 
v_sz_boxed_1707_ = lean_unbox_usize(v_sz_1704_);
lean_dec(v_sz_1704_);
v_i_boxed_1708_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_1707_, v_i_boxed_1708_, v_bs_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_bs_1712_);
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v_bs_x27_1723_; lean_object* v___x_1724_; 
v___x_1720_ = 0;
v_v_1721_ = lean_array_uget(v_bs_1712_, v_i_1711_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v_bs_x27_1723_ = lean_array_uset(v_bs_1712_, v_i_1711_, v___x_1722_);
v___x_1724_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1721_, v___x_1720_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1711_, v___x_1726_);
v___x_1728_ = lean_array_uset(v_bs_x27_1723_, v_i_1711_, v_a_1725_);
v_i_1711_ = v___x_1727_;
v_bs_1712_ = v___x_1728_;
goto _start;
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref(v_bs_x27_1723_);
v_a_1730_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1724_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1724_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_bs_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1746_, v_i_boxed_1747_, v_bs_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1749_, lean_object* v_as_1750_, size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_b_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_a_1760_; uint8_t v___x_1764_; 
v___x_1764_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec(v___x_1749_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_b_1753_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; uint8_t v_kind_1767_; lean_object* v_declName_1768_; lean_object* v_type_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_a_1766_ = lean_array_uget_borrowed(v_as_1750_, v_i_1752_);
v_kind_1767_ = lean_ctor_get_uint8(v_a_1766_, sizeof(void*)*9);
v_declName_1768_ = lean_ctor_get(v_a_1766_, 3);
v_type_1769_ = lean_ctor_get(v_a_1766_, 6);
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_name_eq(v_declName_1768_, v___x_1749_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; 
v___x_1772_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1767_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_inc_ref(v_type_1769_);
v___x_1773_ = l_Lean_Meta_isProp(v_type_1769_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; uint8_t v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = lean_unbox(v_a_1774_);
lean_dec(v_a_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_inc(v___x_1749_);
lean_inc(v_a_1766_);
v___x_1776_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1766_, v___x_1749_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_dec_ref_known(v___x_1776_, 1);
v_a_1760_ = v___x_1770_;
goto v___jp_1759_;
}
else
{
lean_dec(v___x_1749_);
return v___x_1776_;
}
}
else
{
v_a_1760_ = v___x_1770_;
goto v___jp_1759_;
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v___x_1749_);
v_a_1777_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1773_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1773_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
v_a_1760_ = v___x_1770_;
goto v___jp_1759_;
}
}
else
{
v_a_1760_ = v___x_1770_;
goto v___jp_1759_;
}
}
v___jp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1752_, v___x_1761_);
v_i_1752_ = v___x_1762_;
v_b_1753_ = v_a_1760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1785_, lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; lean_object* v_res_1797_; 
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1785_, v_as_1786_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_as_1786_);
return v_res_1797_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1818_, lean_object* v_preDefs_1819_, lean_object* v_termMeasure_x3fs_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v___x_1828_; size_t v_sz_1829_; size_t v___x_1830_; lean_object* v_termMeasures_x3f_1831_; size_t v_sz_1832_; lean_object* v___x_1833_; 
v___x_1828_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_1829_ = lean_array_size(v_termMeasure_x3fs_1820_);
v___x_1830_ = ((size_t)0ULL);
v_termMeasures_x3f_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1829_, v___x_1830_, v_termMeasure_x3fs_1820_);
v_sz_1832_ = lean_array_size(v_preDefs_1819_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1832_, v___x_1830_, v_preDefs_1819_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; size_t v_sz_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___x_1853_; lean_object* v_env_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc_n(v_a_1834_, 2);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = lean_box(0);
v_sz_1849_ = lean_array_size(v_a_1834_);
v___x_1850_ = lean_box_usize(v_sz_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1852_, 0, v_a_1834_);
lean_closure_set(v___f_1852_, 1, v___x_1850_);
lean_closure_set(v___f_1852_, 2, v___x_1851_);
lean_closure_set(v___f_1852_, 3, v___x_1835_);
lean_closure_set(v___f_1852_, 4, v___x_1828_);
v___x_1853_ = lean_st_ref_get(v_a_1826_);
v_env_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc_ref(v_env_1854_);
lean_dec(v___x_1853_);
v___x_1855_ = l_Lean_Environment_unlockAsync(v_env_1854_);
v___x_1856_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1855_, v___f_1852_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v_snd_1858_; lean_object* v_fst_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_2044_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v_snd_1858_ = lean_ctor_get(v_a_1857_, 1);
v_fst_1859_ = lean_ctor_get(v_a_1857_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_1861_ = v_a_1857_;
v_isShared_1862_ = v_isSharedCheck_2044_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1859_);
lean_dec(v_a_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_2044_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_fst_1863_; lean_object* v_snd_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_2043_; 
v_fst_1863_ = lean_ctor_get(v_snd_1858_, 0);
v_snd_1864_ = lean_ctor_get(v_snd_1858_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_snd_1858_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_1866_ = v_snd_1858_;
v_isShared_1867_ = v_isSharedCheck_2043_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_snd_1864_);
lean_inc(v_fst_1863_);
lean_dec(v_snd_1858_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_2043_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___y_1869_; uint8_t v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_wf_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___x_2034_; lean_object* v_a_2035_; uint8_t v___x_2036_; 
lean_inc(v_snd_1864_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1927_, 0, v_snd_1864_);
v___x_1928_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2034_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1928_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = lean_unbox(v_a_2035_);
lean_dec(v_a_2035_);
if (v___x_2036_ == 0)
{
v___y_1997_ = v_a_1821_;
v___y_1998_ = v_a_1822_;
v___y_1999_ = v_a_1823_;
v___y_2000_ = v_a_1824_;
v___y_2001_ = v_a_1825_;
v___y_2002_ = v_a_1826_;
goto v___jp_1996_;
}
else
{
lean_object* v_value_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_value_2037_ = lean_ctor_get(v_snd_1864_, 7);
v___x_2038_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2037_);
v___x_2039_ = l_Lean_MessageData_ofExpr(v_value_2037_);
v___x_2040_ = l_Lean_indentD(v___x_2039_);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1928_, v___x_2041_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_dec_ref_known(v___x_2042_, 1);
v___y_1997_ = v_a_1821_;
v___y_1998_ = v_a_1822_;
v___y_1999_ = v_a_1823_;
v___y_2000_ = v_a_1824_;
v___y_2001_ = v_a_1825_;
v___y_2002_ = v_a_1826_;
goto v___jp_1996_;
}
else
{
lean_dec_ref(v___f_1927_);
lean_del_object(v___x_1866_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_del_object(v___x_1861_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec(v_termMeasures_x3f_1831_);
lean_dec_ref(v_docCtx_1818_);
return v___x_2042_;
}
}
v___jp_1868_:
{
lean_object* v___x_1878_; 
lean_inc_ref(v___y_1871_);
lean_inc(v_a_1834_);
lean_inc(v_fst_1863_);
lean_inc(v_fst_1859_);
v___x_1878_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1859_, v_fst_1863_, v_a_1834_, v___y_1871_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
lean_inc_ref(v___y_1871_);
lean_inc(v_a_1834_);
lean_inc_ref(v_docCtx_1818_);
v___x_1880_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1818_, v_a_1834_, v_a_1879_, v___y_1871_, v___y_1870_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v_a_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1881_; 
lean_dec_ref_known(v___x_1880_, 1);
lean_inc(v_a_1834_);
v___x_1881_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1818_, v_a_1834_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref_known(v___x_1881_, 1);
v___x_1882_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1864_, v___y_1870_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1849_, v___x_1830_, v_a_1834_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_declName_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc_n(v_a_1885_, 2);
lean_dec_ref_known(v___x_1884_, 1);
v_declName_1886_ = lean_ctor_get(v___y_1871_, 3);
lean_inc_n(v_declName_1886_, 2);
lean_dec_ref(v___y_1871_);
v___x_1887_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1885_, v_declName_1886_, v_fst_1859_, v_fst_1863_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_declName_1888_; lean_object* v_type_1889_; lean_object* v___x_1890_; 
lean_dec_ref_known(v___x_1887_, 1);
v_declName_1888_ = lean_ctor_get(v_a_1883_, 3);
v_type_1889_ = lean_ctor_get(v_a_1883_, 6);
lean_inc(v_declName_1888_);
v___x_1890_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1888_, v___y_1877_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref_known(v___x_1890_, 1);
lean_inc_ref(v_type_1889_);
v___x_1891_ = l_Lean_Meta_isProp(v_type_1889_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; uint8_t v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = lean_unbox(v_a_1892_);
lean_dec(v_a_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_inc(v_declName_1886_);
v___x_1894_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1883_, v_declName_1886_, v___y_1869_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_dec_ref_known(v___x_1894_, 1);
v___y_1837_ = v_declName_1886_;
v___y_1838_ = v_a_1885_;
v___y_1839_ = v___y_1872_;
v___y_1840_ = v___y_1873_;
v___y_1841_ = v___y_1874_;
v___y_1842_ = v___y_1875_;
v___y_1843_ = v___y_1876_;
v___y_1844_ = v___y_1877_;
goto v___jp_1836_;
}
else
{
lean_dec(v_declName_1886_);
lean_dec(v_a_1885_);
return v___x_1894_;
}
}
else
{
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1869_);
v___y_1837_ = v_declName_1886_;
v___y_1838_ = v_a_1885_;
v___y_1839_ = v___y_1872_;
v___y_1840_ = v___y_1873_;
v___y_1841_ = v___y_1874_;
v___y_1842_ = v___y_1875_;
v___y_1843_ = v___y_1876_;
v___y_1844_ = v___y_1877_;
goto v___jp_1836_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_declName_1886_);
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1869_);
v_a_1895_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1891_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1891_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_dec(v_declName_1886_);
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1869_);
return v___x_1890_;
}
}
else
{
lean_dec(v_declName_1886_);
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1869_);
return v___x_1887_;
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
v_a_1903_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1884_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1884_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
v_a_1911_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1882_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1882_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
return v___x_1881_;
}
}
else
{
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec_ref(v_docCtx_1818_);
return v___x_1880_;
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec_ref(v_docCtx_1818_);
v_a_1919_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1878_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1878_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
v___jp_1929_:
{
lean_object* v_declName_1939_; lean_object* v_type_1940_; lean_object* v_numFixed_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; 
v_declName_1939_ = lean_ctor_get(v_snd_1864_, 3);
v_type_1940_ = lean_ctor_get(v_snd_1864_, 6);
v_numFixed_1941_ = lean_ctor_get(v_fst_1859_, 0);
v___x_1942_ = lean_box_usize(v_sz_1849_);
v___x_1943_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1859_);
lean_inc(v_declName_1939_);
lean_inc(v_fst_1863_);
lean_inc(v_snd_1864_);
lean_inc(v_a_1834_);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1944_, 0, v___x_1942_);
lean_closure_set(v___f_1944_, 1, v___x_1943_);
lean_closure_set(v___f_1944_, 2, v_a_1834_);
lean_closure_set(v___f_1944_, 3, v___y_1930_);
lean_closure_set(v___f_1944_, 4, v_snd_1864_);
lean_closure_set(v___f_1944_, 5, v_fst_1863_);
lean_closure_set(v___f_1944_, 6, v___x_1835_);
lean_closure_set(v___f_1944_, 7, v___x_1928_);
lean_closure_set(v___f_1944_, 8, v_declName_1939_);
lean_closure_set(v___f_1944_, 9, v_fst_1859_);
lean_closure_set(v___f_1944_, 10, v_wf_1932_);
lean_inc(v_numFixed_1941_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_numFixed_1941_);
v___x_1946_ = 0;
lean_inc_ref(v_type_1940_);
v___x_1947_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1940_, v___x_1945_, v___f_1944_, v___x_1946_, v___x_1946_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v_a_1950_; uint8_t v___x_1951_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1928_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = lean_unbox(v_a_1950_);
lean_dec(v_a_1950_);
if (v___x_1951_ == 0)
{
lean_del_object(v___x_1866_);
lean_del_object(v___x_1861_);
v___y_1869_ = v___y_1931_;
v___y_1870_ = v___x_1946_;
v___y_1871_ = v_a_1948_;
v___y_1872_ = v___y_1933_;
v___y_1873_ = v___y_1934_;
v___y_1874_ = v___y_1935_;
v___y_1875_ = v___y_1936_;
v___y_1876_ = v___y_1937_;
v___y_1877_ = v___y_1938_;
goto v___jp_1868_;
}
else
{
lean_object* v_declName_1952_; lean_object* v_value_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v_declName_1952_ = lean_ctor_get(v_a_1948_, 3);
v_value_1953_ = lean_ctor_get(v_a_1948_, 7);
v___x_1954_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1952_);
v___x_1955_ = l_Lean_MessageData_ofName(v_declName_1952_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 7);
lean_ctor_set(v___x_1866_, 1, v___x_1955_);
lean_ctor_set(v___x_1866_, 0, v___x_1954_);
v___x_1957_ = v___x_1866_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 7);
lean_ctor_set(v___x_1861_, 1, v___x_1958_);
lean_ctor_set(v___x_1861_, 0, v___x_1957_);
v___x_1960_ = v___x_1861_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_inc_ref(v_value_1953_);
v___x_1961_ = l_Lean_MessageData_ofExpr(v_value_1953_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1928_, v___x_1962_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
v___y_1869_ = v___y_1931_;
v___y_1870_ = v___x_1946_;
v___y_1871_ = v_a_1948_;
v___y_1872_ = v___y_1933_;
v___y_1873_ = v___y_1934_;
v___y_1874_ = v___y_1935_;
v___y_1875_ = v___y_1936_;
v___y_1876_ = v___y_1937_;
v___y_1877_ = v___y_1938_;
goto v___jp_1868_;
}
else
{
lean_dec(v_a_1948_);
lean_dec_ref(v___y_1931_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec_ref(v_docCtx_1818_);
return v___x_1963_;
}
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___y_1931_);
lean_del_object(v___x_1866_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_del_object(v___x_1861_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec_ref(v_docCtx_1818_);
v_a_1966_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1947_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1947_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
v___jp_1974_:
{
if (lean_obj_tag(v_termMeasures_x3f_1831_) == 1)
{
lean_object* v_val_1984_; 
lean_dec_ref(v___y_1977_);
v_val_1984_ = lean_ctor_get(v_termMeasures_x3f_1831_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v_termMeasures_x3f_1831_, 1);
v___y_1930_ = v___y_1976_;
v___y_1931_ = v___y_1975_;
v_wf_1932_ = v_val_1984_;
v___y_1933_ = v___y_1978_;
v___y_1934_ = v___y_1979_;
v___y_1935_ = v___y_1980_;
v___y_1936_ = v___y_1981_;
v___y_1937_ = v___y_1982_;
v___y_1938_ = v___y_1983_;
goto v___jp_1929_;
}
else
{
uint8_t v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v_termMeasures_x3f_1831_);
v___x_1985_ = 1;
v___x_1986_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1977_, v___x_1985_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___y_1930_ = v___y_1976_;
v___y_1931_ = v___y_1975_;
v_wf_1932_ = v_a_1987_;
v___y_1933_ = v___y_1978_;
v___y_1934_ = v___y_1979_;
v___y_1935_ = v___y_1980_;
v___y_1936_ = v___y_1981_;
v___y_1937_ = v___y_1982_;
v___y_1938_ = v___y_1983_;
goto v___jp_1929_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_del_object(v___x_1866_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_del_object(v___x_1861_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec_ref(v_docCtx_1818_);
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
v___jp_1996_:
{
lean_object* v___x_2003_; lean_object* v_env_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2003_ = lean_st_ref_get(v___y_2002_);
v_env_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc_ref(v_env_2004_);
lean_dec(v___x_2003_);
v___x_2005_ = l_Lean_Environment_unlockAsync(v_env_2004_);
v___x_2006_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_2005_, v___f_1927_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2025_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_fst_2008_ = lean_ctor_get(v_a_2007_, 0);
v_snd_2009_ = lean_ctor_get(v_a_2007_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2011_ = v_a_2007_;
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2008_);
lean_dec(v_a_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v_a_2015_; uint8_t v___x_2016_; 
lean_inc(v_fst_1863_);
lean_inc(v_fst_1859_);
lean_inc(v_fst_2008_);
lean_inc(v_a_1834_);
v___f_2013_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2013_, 0, v_a_1834_);
lean_closure_set(v___f_2013_, 1, v_fst_2008_);
lean_closure_set(v___f_2013_, 2, v_fst_1859_);
lean_closure_set(v___f_2013_, 3, v_fst_1863_);
v___x_2014_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1928_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
if (v___x_2016_ == 0)
{
lean_del_object(v___x_2011_);
v___y_1975_ = v_snd_2009_;
v___y_1976_ = v_fst_2008_;
v___y_1977_ = v___f_2013_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2001_;
v___y_1983_ = v___y_2002_;
goto v___jp_1974_;
}
else
{
lean_object* v_value_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v_value_2017_ = lean_ctor_get(v_snd_1864_, 7);
v___x_2018_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2017_);
v___x_2019_ = l_Lean_MessageData_ofExpr(v_value_2017_);
v___x_2020_ = l_Lean_indentD(v___x_2019_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 7);
lean_ctor_set(v___x_2011_, 1, v___x_2020_);
lean_ctor_set(v___x_2011_, 0, v___x_2018_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1928_, v___x_2022_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_dec_ref_known(v___x_2023_, 1);
v___y_1975_ = v_snd_2009_;
v___y_1976_ = v_fst_2008_;
v___y_1977_ = v___f_2013_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2001_;
v___y_1983_ = v___y_2002_;
goto v___jp_1974_;
}
else
{
lean_dec_ref(v___f_2013_);
lean_dec(v_snd_2009_);
lean_dec(v_fst_2008_);
lean_del_object(v___x_1866_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_del_object(v___x_1861_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec(v_termMeasures_x3f_1831_);
lean_dec_ref(v_docCtx_1818_);
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_del_object(v___x_1866_);
lean_dec(v_snd_1864_);
lean_dec(v_fst_1863_);
lean_del_object(v___x_1861_);
lean_dec(v_fst_1859_);
lean_dec(v_a_1834_);
lean_dec(v_termMeasures_x3f_1831_);
lean_dec_ref(v_docCtx_1818_);
v_a_2026_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2006_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2006_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_1834_);
lean_dec(v_termMeasures_x3f_1831_);
lean_dec_ref(v_docCtx_1818_);
v_a_2045_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_1856_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_1856_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
v___jp_1836_:
{
size_t v_sz_1845_; lean_object* v___x_1846_; 
v_sz_1845_ = lean_array_size(v___y_1838_);
lean_inc(v___y_1837_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1837_, v___y_1838_, v_sz_1845_, v___x_1830_, v___x_1835_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; 
lean_dec_ref_known(v___x_1846_, 1);
v___x_1847_ = l_Lean_enableRealizationsForConst(v___y_1837_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref_known(v___x_1847_, 1);
v___x_1848_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1848_;
}
else
{
lean_dec_ref(v___y_1838_);
return v___x_1847_;
}
}
else
{
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
return v___x_1846_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_termMeasures_x3f_1831_);
lean_dec_ref(v_docCtx_1818_);
v_a_2053_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_1833_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_1833_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2061_, lean_object* v_preDefs_2062_, lean_object* v_termMeasure_x3fs_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Elab_wfRecursion(v_docCtx_2061_, v_preDefs_2062_, v_termMeasure_x3fs_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2072_, lean_object* v_msg_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_msg_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2082_, v_msg_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_bs_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_2092_, v_i_2093_, v_bs_2094_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_sz_2103_, lean_object* v_i_2104_, lean_object* v_bs_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
size_t v_sz_boxed_2113_; size_t v_i_boxed_2114_; lean_object* v_res_2115_; 
v_sz_boxed_2113_ = lean_unbox_usize(v_sz_2103_);
lean_dec(v_sz_2103_);
v_i_boxed_2114_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_boxed_2113_, v_i_boxed_2114_, v_bs_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_as_2116_, size_t v_sz_2117_, size_t v_i_2118_, lean_object* v_b_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_2116_, v_sz_2117_, v_i_2118_, v_b_2119_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_as_2128_, lean_object* v_sz_2129_, lean_object* v_i_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
size_t v_sz_boxed_2139_; size_t v_i_boxed_2140_; lean_object* v_res_2141_; 
v_sz_boxed_2139_ = lean_unbox_usize(v_sz_2129_);
lean_dec(v_sz_2129_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2128_, v_sz_boxed_2139_, v_i_boxed_2140_, v_b_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_a_2142_, lean_object* v_as_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_bs_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_2142_, v_sz_2144_, v_i_2145_, v_bs_2146_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_a_2155_, lean_object* v_as_2156_, lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_bs_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2155_, v_as_2156_, v_sz_boxed_2167_, v_i_boxed_2168_, v_bs_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v_as_2156_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_a_2170_, lean_object* v___x_2171_, size_t v_sz_2172_, size_t v_i_2173_, lean_object* v_bs_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_2170_, v___x_2171_, v_sz_2172_, v_i_2173_, v_bs_2174_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_a_2183_, lean_object* v___x_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_bs_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
size_t v_sz_boxed_2195_; size_t v_i_boxed_2196_; lean_object* v_res_2197_; 
v_sz_boxed_2195_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2196_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2183_, v___x_2184_, v_sz_boxed_2195_, v_i_boxed_2196_, v_bs_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_00_u03b1_2198_, lean_object* v_env_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_2199_, v_x_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_00_u03b1_2209_, lean_object* v_env_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(v_00_u03b1_2209_, v_env_2210_, v_x_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2220_, v_msg_2221_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2230_, lean_object* v_msg_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2230_, v_msg_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2240_, size_t v_i_2241_, lean_object* v_bs_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2240_, v_i_2241_, v_bs_2242_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2251_, lean_object* v_i_2252_, lean_object* v_bs_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2251_);
lean_dec(v_sz_2251_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2261_, v_i_boxed_2262_, v_bs_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2264_, lean_object* v_as_2265_, size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2264_, v_as_2265_, v_sz_2266_, v_i_2267_, v_b_2268_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2277_, lean_object* v_as_2278_, lean_object* v_sz_2279_, lean_object* v_i_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
size_t v_sz_boxed_2289_; size_t v_i_boxed_2290_; lean_object* v_res_2291_; 
v_sz_boxed_2289_ = lean_unbox_usize(v_sz_2279_);
lean_dec(v_sz_2279_);
v_i_boxed_2290_ = lean_unbox_usize(v_i_2280_);
lean_dec(v_i_2280_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2277_, v_as_2278_, v_sz_boxed_2289_, v_i_boxed_2290_, v_b_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v_as_2278_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2292_, lean_object* v_x_2293_, uint8_t v_isExporting_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2293_, v_isExporting_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_x_2304_, lean_object* v_isExporting_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v_isExporting_boxed_2313_; lean_object* v_res_2314_; 
v_isExporting_boxed_2313_ = lean_unbox(v_isExporting_2305_);
v_res_2314_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2303_, v_x_2304_, v_isExporting_boxed_2313_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2315_, lean_object* v_x_2316_, uint8_t v_when_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2316_, v_when_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2326_, lean_object* v_x_2327_, lean_object* v_when_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v_when_boxed_2336_; lean_object* v_res_2337_; 
v_when_boxed_2336_ = lean_unbox(v_when_2328_);
v_res_2337_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2326_, v_x_2327_, v_when_boxed_2336_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2338_, lean_object* v_macroStack_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2338_, v_macroStack_2339_, v___y_2344_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2348_, lean_object* v_macroStack_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2348_, v_macroStack_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2358_, lean_object* v_msgData_2359_, uint8_t v_severity_2360_, uint8_t v_isSilent_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2358_, v_msgData_2359_, v_severity_2360_, v_isSilent_2361_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2370_, lean_object* v_msgData_2371_, lean_object* v_severity_2372_, lean_object* v_isSilent_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v_severity_boxed_2381_; uint8_t v_isSilent_boxed_2382_; lean_object* v_res_2383_; 
v_severity_boxed_2381_ = lean_unbox(v_severity_2372_);
v_isSilent_boxed_2382_ = lean_unbox(v_isSilent_2373_);
v_res_2383_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2370_, v_msgData_2371_, v_severity_boxed_2381_, v_isSilent_boxed_2382_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_ref_2370_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2454_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2455_ = 0;
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2457_ = l_Lean_registerTraceClass(v___x_2454_, v___x_2455_, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2459_;
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
