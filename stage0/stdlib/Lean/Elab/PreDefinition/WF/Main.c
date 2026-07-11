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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "well-founded recursion cannot be used, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not take any (non-fixed) arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_wfRecursion___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_wfRecursion___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_12_; lean_object* v_nextMacroScope_13_; lean_object* v_ngen_14_; lean_object* v_auxDeclNGen_15_; lean_object* v_traceState_16_; lean_object* v_messages_17_; lean_object* v_infoState_18_; lean_object* v_snapshotTasks_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_45_; 
v___x_12_ = lean_st_ref_take(v___y_10_);
v_nextMacroScope_13_ = lean_ctor_get(v___x_12_, 1);
v_ngen_14_ = lean_ctor_get(v___x_12_, 2);
v_auxDeclNGen_15_ = lean_ctor_get(v___x_12_, 3);
v_traceState_16_ = lean_ctor_get(v___x_12_, 4);
v_messages_17_ = lean_ctor_get(v___x_12_, 6);
v_infoState_18_ = lean_ctor_get(v___x_12_, 7);
v_snapshotTasks_19_ = lean_ctor_get(v___x_12_, 8);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; lean_object* v_unused_47_; 
v_unused_46_ = lean_ctor_get(v___x_12_, 5);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_47_);
v___x_21_ = v___x_12_;
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snapshotTasks_19_);
lean_inc(v_infoState_18_);
lean_inc(v_messages_17_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_15_);
lean_inc(v_ngen_14_);
lean_inc(v_nextMacroScope_13_);
lean_dec(v___x_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 5, v___x_23_);
lean_ctor_set(v___x_21_, 0, v_env_8_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_env_8_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_nextMacroScope_13_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_ngen_14_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_auxDeclNGen_15_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_traceState_16_);
lean_ctor_set(v_reuseFailAlloc_44_, 5, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_44_, 6, v_messages_17_);
lean_ctor_set(v_reuseFailAlloc_44_, 7, v_infoState_18_);
lean_ctor_set(v_reuseFailAlloc_44_, 8, v_snapshotTasks_19_);
v___x_25_ = v_reuseFailAlloc_44_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v_zetaDeltaFVarIds_29_; lean_object* v_postponed_30_; lean_object* v_diag_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
v___x_26_ = lean_st_ref_set(v___y_10_, v___x_25_);
v___x_27_ = lean_st_ref_take(v___y_9_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
v_zetaDeltaFVarIds_29_ = lean_ctor_get(v___x_27_, 2);
v_postponed_30_ = lean_ctor_get(v___x_27_, 3);
v_diag_31_ = lean_ctor_get(v___x_27_, 4);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_27_, 1);
lean_dec(v_unused_43_);
v___x_33_ = v___x_27_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_diag_31_);
lean_inc(v_postponed_30_);
lean_inc(v_zetaDeltaFVarIds_29_);
lean_inc(v_mctx_28_);
lean_dec(v___x_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_mctx_28_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_zetaDeltaFVarIds_29_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v_postponed_30_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v_diag_31_);
v___x_37_ = v_reuseFailAlloc_41_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_st_ref_set(v___y_9_, v___x_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec(v___y_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_53_, v___y_57_, v___y_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v_b_74_, lean_object* v_c_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
lean_inc(v___y_73_);
lean_inc_ref(v___y_72_);
v___x_81_ = lean_apply_9(v_k_71_, v_b_74_, v_c_75_, v___y_72_, v___y_73_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v_b_85_, lean_object* v_c_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_82_, v___y_83_, v___y_84_, v_b_85_, v_c_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_93_, lean_object* v_maxFVars_x3f_94_, lean_object* v_k_95_, uint8_t v_cleanupAnnotations_96_, uint8_t v_whnfType_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_105_, 0, v_k_95_);
lean_closure_set(v___f_105_, 1, v___y_98_);
lean_closure_set(v___f_105_, 2, v___y_99_);
v___x_106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_93_, v_maxFVars_x3f_94_, v___f_105_, v_cleanupAnnotations_96_, v_whnfType_97_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_115_, lean_object* v_maxFVars_x3f_116_, lean_object* v_k_117_, lean_object* v_cleanupAnnotations_118_, lean_object* v_whnfType_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_127_; uint8_t v_whnfType_boxed_128_; lean_object* v_res_129_; 
v_cleanupAnnotations_boxed_127_ = lean_unbox(v_cleanupAnnotations_118_);
v_whnfType_boxed_128_ = lean_unbox(v_whnfType_119_);
v_res_129_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_115_, v_maxFVars_x3f_116_, v_k_117_, v_cleanupAnnotations_boxed_127_, v_whnfType_boxed_128_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_130_, lean_object* v_type_131_, lean_object* v_maxFVars_x3f_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, uint8_t v_whnfType_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_131_, v_maxFVars_x3f_132_, v_k_133_, v_cleanupAnnotations_134_, v_whnfType_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_144_, lean_object* v_type_145_, lean_object* v_maxFVars_x3f_146_, lean_object* v_k_147_, lean_object* v_cleanupAnnotations_148_, lean_object* v_whnfType_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_157_; uint8_t v_whnfType_boxed_158_; lean_object* v_res_159_; 
v_cleanupAnnotations_boxed_157_ = lean_unbox(v_cleanupAnnotations_148_);
v_whnfType_boxed_158_ = lean_unbox(v_whnfType_149_);
v_res_159_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_144_, v_type_145_, v_maxFVars_x3f_146_, v_k_147_, v_cleanupAnnotations_boxed_157_, v_whnfType_boxed_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_159_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(1);
v___x_161_ = l_Lean_MessageData_ofFormat(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
return v_x_167_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_192_; 
v_head_169_ = lean_ctor_get(v_x_168_, 0);
v_tail_170_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_192_ == 0)
{
v___x_172_ = v_x_168_;
v_isShared_173_ = v_isSharedCheck_192_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_tail_170_);
lean_inc(v_head_169_);
lean_dec(v_x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_192_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_before_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_190_; 
v_before_174_ = lean_ctor_get(v_head_169_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_head_169_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v_head_169_, 1);
lean_dec(v_unused_191_);
v___x_176_ = v_head_169_;
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_before_174_);
lean_dec(v_head_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_190_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 7);
lean_ctor_set(v___x_176_, 1, v___x_178_);
lean_ctor_set(v___x_176_, 0, v_x_167_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_x_167_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_189_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 7);
lean_ctor_set(v___x_172_, 1, v___x_181_);
lean_ctor_set(v___x_172_, 0, v___x_180_);
v___x_183_ = v___x_172_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_188_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = l_Lean_MessageData_ofSyntax(v_before_174_);
v___x_185_ = l_Lean_indentD(v___x_184_);
v___x_186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_183_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v_x_167_ = v___x_186_;
v_x_168_ = v_tail_170_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_193_, lean_object* v_opt_194_){
_start:
{
lean_object* v_name_195_; lean_object* v_defValue_196_; lean_object* v_map_197_; lean_object* v___x_198_; 
v_name_195_ = lean_ctor_get(v_opt_194_, 0);
v_defValue_196_ = lean_ctor_get(v_opt_194_, 1);
v_map_197_ = lean_ctor_get(v_opts_193_, 0);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_197_, v_name_195_);
if (lean_obj_tag(v___x_198_) == 0)
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_defValue_196_);
return v___x_199_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___x_198_, 1);
if (lean_obj_tag(v_val_200_) == 1)
{
uint8_t v_v_201_; 
v_v_201_ = lean_ctor_get_uint8(v_val_200_, 0);
lean_dec_ref_known(v_val_200_, 0);
return v_v_201_;
}
else
{
uint8_t v___x_202_; 
lean_dec(v_val_200_);
v___x_202_ = lean_unbox(v_defValue_196_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_203_, lean_object* v_opt_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_203_, v_opt_204_);
lean_dec_ref(v_opt_204_);
lean_dec_ref(v_opts_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_212_, lean_object* v_macroStack_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_options_216_; lean_object* v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; 
v_options_216_ = lean_ctor_get(v___y_214_, 2);
v___x_217_ = l_Lean_Elab_pp_macroStack;
v___x_218_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_216_, v___x_217_);
v___x_219_ = lean_bool_not(v___x_218_);
if (v___x_219_ == 0)
{
if (lean_obj_tag(v_macroStack_213_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_msgData_212_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_after_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_237_; 
v_head_221_ = lean_ctor_get(v_macroStack_213_, 0);
lean_inc(v_head_221_);
v_after_222_ = lean_ctor_get(v_head_221_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_head_221_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_head_221_, 0);
lean_dec(v_unused_238_);
v___x_224_ = v_head_221_;
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_after_222_);
lean_dec(v_head_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 7);
lean_ctor_set(v___x_224_, 1, v___x_226_);
lean_ctor_set(v___x_224_, 0, v_msgData_212_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_msgData_212_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_236_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_msgData_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_229_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_MessageData_ofSyntax(v_after_222_);
v___x_232_ = l_Lean_indentD(v___x_231_);
v_msgData_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_233_, 0, v___x_230_);
lean_ctor_set(v_msgData_233_, 1, v___x_232_);
v___x_234_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_233_, v_macroStack_213_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_macroStack_213_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_msgData_212_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_240_, lean_object* v_macroStack_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_240_, v_macroStack_241_, v___y_242_);
lean_dec_ref(v___y_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v_mctx_254_; lean_object* v_lctx_255_; lean_object* v_options_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_251_ = lean_st_ref_get(v___y_249_);
v_env_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_env_252_);
lean_dec(v___x_251_);
v___x_253_ = lean_st_ref_get(v___y_247_);
v_mctx_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_254_);
lean_dec(v___x_253_);
v_lctx_255_ = lean_ctor_get(v___y_246_, 2);
v_options_256_ = lean_ctor_get(v___y_248_, 2);
lean_inc_ref(v_options_256_);
lean_inc_ref(v_lctx_255_);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_env_252_);
lean_ctor_set(v___x_257_, 1, v_mctx_254_);
lean_ctor_set(v___x_257_, 2, v_lctx_255_);
lean_ctor_set(v___x_257_, 3, v_options_256_);
v___x_258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_msgData_245_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v_macroStack_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_ref_275_ = lean_ctor_get(v___y_272_, 5);
v___x_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_267_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v_macroStack_278_ = lean_ctor_get(v___y_268_, 1);
v___x_279_ = l_Lean_Elab_getBetterRef(v_ref_275_, v_macroStack_278_);
lean_inc(v_macroStack_278_);
v___x_280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_277_, v_macroStack_278_, v___y_272_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_279_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_as_305_, size_t v_sz_306_, size_t v_i_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_a_317_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_307_, v_sz_306_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_b_308_);
return v___x_322_;
}
else
{
lean_object* v_array_323_; lean_object* v_start_324_; lean_object* v_stop_325_; uint8_t v___x_326_; 
v_array_323_ = lean_ctor_get(v_b_308_, 0);
v_start_324_ = lean_ctor_get(v_b_308_, 1);
v_stop_325_ = lean_ctor_get(v_b_308_, 2);
v___x_326_ = lean_nat_dec_lt(v_start_324_, v_stop_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_b_308_);
return v___x_327_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_356_; 
lean_inc(v_stop_325_);
lean_inc(v_start_324_);
lean_inc_ref(v_array_323_);
v_isSharedCheck_356_ = !lean_is_exclusive(v_b_308_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_357_ = lean_ctor_get(v_b_308_, 2);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_b_308_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_b_308_, 0);
lean_dec(v_unused_359_);
v___x_329_ = v_b_308_;
v_isShared_330_ = v_isSharedCheck_356_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_b_308_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_356_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v_a_331_ = lean_array_uget_borrowed(v_as_305_, v_i_307_);
v___x_332_ = lean_array_fget(v_array_323_, v_start_324_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_start_324_, v___x_333_);
lean_dec(v_start_324_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_334_);
v___x_336_ = v___x_329_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_array_323_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_stop_325_);
v___x_336_ = v_reuseFailAlloc_355_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_array_get_size(v_a_331_);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v___x_332_);
v_a_317_ = v___x_336_;
goto v___jp_316_;
}
else
{
lean_object* v_declName_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_declName_340_ = lean_ctor_get(v___x_332_, 3);
lean_inc(v_declName_340_);
lean_dec(v___x_332_);
v___x_341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
v___x_342_ = l_Lean_MessageData_ofName(v_declName_340_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_345_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec_ref_known(v___x_346_, 1);
v_a_317_ = v___x_336_;
goto v___jp_316_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___x_336_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
}
}
v___jp_316_:
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_307_, v___x_318_);
v_i_307_ = v___x_319_;
v_b_308_ = v_a_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_as_360_, lean_object* v_sz_361_, lean_object* v_i_362_, lean_object* v_b_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_361_);
lean_dec(v_sz_361_);
v_i_boxed_372_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_360_, v_sz_boxed_371_, v_i_boxed_372_, v_b_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec_ref(v_as_360_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_bs_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec_ref(v_a_374_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_bs_377_);
return v___x_384_;
}
else
{
lean_object* v_v_385_; lean_object* v___x_386_; lean_object* v_bs_x27_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_v_385_ = lean_array_uget(v_bs_377_, v_i_376_);
v___x_386_ = lean_unsigned_to_nat(0u);
v_bs_x27_387_ = lean_array_uset(v_bs_377_, v_i_376_, v___x_386_);
v___x_388_ = lean_usize_to_nat(v_i_376_);
lean_inc_ref(v_a_374_);
v___x_389_ = l_Lean_Elab_WF_varyingVarNames(v_a_374_, v___x_388_, v_v_385_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_376_, v___x_391_);
v___x_393_ = lean_array_uset(v_bs_x27_387_, v_i_376_, v_a_390_);
v_i_376_ = v___x_392_;
v_bs_377_ = v___x_393_;
goto _start;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_bs_x27_387_);
lean_dec_ref(v_a_374_);
v_a_395_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_403_, lean_object* v_sz_404_, lean_object* v_i_405_, lean_object* v_bs_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
size_t v_sz_boxed_412_; size_t v_i_boxed_413_; lean_object* v_res_414_; 
v_sz_boxed_412_ = lean_unbox_usize(v_sz_404_);
lean_dec(v_sz_404_);
v_i_boxed_413_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_403_, v_sz_boxed_412_, v_i_boxed_413_, v_bs_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object* v_as_415_, size_t v_sz_416_, size_t v_i_417_, lean_object* v_b_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_417_, v_sz_416_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_b_418_);
return v___x_423_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_array_uget_borrowed(v_as_415_, v_i_417_);
v___x_425_ = l_Lean_Elab_addAsAxiom___redArg(v_a_424_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
lean_dec_ref_known(v___x_425_, 1);
v___x_426_ = lean_box(0);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_417_, v___x_427_);
v_i_417_ = v___x_428_;
v_b_418_ = v___x_426_;
goto _start;
}
else
{
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_as_430_, lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_b_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
size_t v_sz_boxed_437_; size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_sz_boxed_437_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_438_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_430_, v_sz_boxed_437_, v_i_boxed_438_, v_b_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v_as_430_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
return v_bs_442_;
}
else
{
lean_object* v_v_444_; lean_object* v_declName_445_; lean_object* v___x_446_; lean_object* v_bs_x27_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget_borrowed(v_bs_442_, v_i_441_);
v_declName_445_ = lean_ctor_get(v_v_444_, 3);
lean_inc(v_declName_445_);
v___x_446_ = lean_unsigned_to_nat(0u);
v_bs_x27_447_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_447_, v_i_441_, v_declName_445_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object* v_a_458_, lean_object* v___x_459_, size_t v_sz_460_, size_t v_i_461_, lean_object* v_bs_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_461_, v_sz_460_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec(v___x_459_);
lean_dec_ref(v_a_458_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_bs_462_);
return v___x_467_;
}
else
{
lean_object* v_v_468_; lean_object* v_ref_469_; uint8_t v_kind_470_; lean_object* v_levelParams_471_; lean_object* v_modifiers_472_; lean_object* v_declName_473_; lean_object* v_binders_474_; lean_object* v_numSectionVars_475_; lean_object* v_type_476_; lean_object* v_value_477_; lean_object* v_termination_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_504_; 
v_v_468_ = lean_array_uget(v_bs_462_, v_i_461_);
v_ref_469_ = lean_ctor_get(v_v_468_, 0);
v_kind_470_ = lean_ctor_get_uint8(v_v_468_, sizeof(void*)*9);
v_levelParams_471_ = lean_ctor_get(v_v_468_, 1);
v_modifiers_472_ = lean_ctor_get(v_v_468_, 2);
v_declName_473_ = lean_ctor_get(v_v_468_, 3);
v_binders_474_ = lean_ctor_get(v_v_468_, 4);
v_numSectionVars_475_ = lean_ctor_get(v_v_468_, 5);
v_type_476_ = lean_ctor_get(v_v_468_, 6);
v_value_477_ = lean_ctor_get(v_v_468_, 7);
v_termination_478_ = lean_ctor_get(v_v_468_, 8);
v_isSharedCheck_504_ = !lean_is_exclusive(v_v_468_);
if (v_isSharedCheck_504_ == 0)
{
v___x_480_ = v_v_468_;
v_isShared_481_ = v_isSharedCheck_504_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_termination_478_);
lean_inc(v_value_477_);
lean_inc(v_type_476_);
lean_inc(v_numSectionVars_475_);
lean_inc(v_binders_474_);
lean_inc(v_declName_473_);
lean_inc(v_modifiers_472_);
lean_inc(v_levelParams_471_);
lean_inc(v_ref_469_);
lean_dec(v_v_468_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_504_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
size_t v_sz_482_; size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_sz_482_ = lean_array_size(v_a_458_);
v___x_483_ = ((size_t)0ULL);
lean_inc_ref(v_a_458_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_482_, v___x_483_, v_a_458_);
lean_inc(v___x_459_);
v___x_485_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_484_, v___x_459_, v_value_477_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; lean_object* v_bs_x27_488_; lean_object* v___x_490_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_unsigned_to_nat(0u);
v_bs_x27_488_ = lean_array_uset(v_bs_462_, v_i_461_, v___x_487_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 7, v_a_486_);
v___x_490_ = v___x_480_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_ref_469_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_levelParams_471_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_modifiers_472_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_declName_473_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_binders_474_);
lean_ctor_set(v_reuseFailAlloc_495_, 5, v_numSectionVars_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 6, v_type_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 7, v_a_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 8, v_termination_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*9, v_kind_470_);
v___x_490_ = v_reuseFailAlloc_495_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_461_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_488_, v_i_461_, v___x_490_);
v_i_461_ = v___x_492_;
v_bs_462_ = v___x_493_;
goto _start;
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_480_);
lean_dec_ref(v_termination_478_);
lean_dec_ref(v_type_476_);
lean_dec(v_numSectionVars_475_);
lean_dec(v_binders_474_);
lean_dec(v_declName_473_);
lean_dec_ref(v_modifiers_472_);
lean_dec(v_levelParams_471_);
lean_dec(v_ref_469_);
lean_dec_ref(v_bs_462_);
lean_dec(v___x_459_);
lean_dec_ref(v_a_458_);
v_a_496_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_485_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_485_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* v_a_505_, lean_object* v___x_506_, lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_sz_boxed_513_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_514_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_505_, v___x_506_, v_sz_boxed_513_, v_i_boxed_514_, v_bs_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_516_, size_t v_sz_517_, size_t v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_516_, v_sz_517_, v___x_518_, v___x_519_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; 
lean_dec_ref_known(v___x_528_, 1);
lean_inc_ref(v_a_516_);
v___x_529_ = l_Lean_Elab_getFixedParamPerms(v_a_516_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_n(v_a_530_, 2);
lean_dec_ref_known(v___x_529_, 1);
lean_inc_ref(v_a_516_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_530_, v_sz_517_, v___x_518_, v_a_516_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; size_t v_sz_536_; lean_object* v___x_537_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_array_get_size(v_a_516_);
lean_inc_ref(v_a_516_);
v___x_535_ = l_Array_toSubarray___redArg(v_a_516_, v___x_533_, v___x_534_);
v_sz_536_ = lean_array_size(v_a_532_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_532_, v_sz_536_, v___x_518_, v___x_535_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v_numSectionVars_539_; lean_object* v___x_540_; 
lean_dec_ref_known(v___x_537_, 1);
v___x_538_ = lean_array_get_borrowed(v___x_520_, v_a_516_, v___x_533_);
v_numSectionVars_539_ = lean_ctor_get(v___x_538_, 5);
lean_inc(v_numSectionVars_539_);
lean_inc_ref(v_a_516_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_516_, v_numSectionVars_539_, v_sz_517_, v___x_518_, v_a_516_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
lean_inc(v_a_532_);
lean_inc(v_a_530_);
v___x_542_ = l_Lean_Elab_WF_packMutual(v_a_530_, v_a_532_, v_a_541_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_552_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_552_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_a_532_);
lean_ctor_set(v___x_547_, 1, v_a_543_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_a_530_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_532_);
lean_dec(v_a_530_);
v_a_553_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_542_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_542_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_532_);
lean_dec(v_a_530_);
v_a_561_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_540_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_540_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_532_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_516_);
v_a_569_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_537_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_537_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_530_);
lean_dec_ref(v_a_516_);
v_a_577_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_531_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_531_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_a_516_);
v_a_585_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_529_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_529_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_a_516_);
v_a_593_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_528_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_528_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_601_, lean_object* v_sz_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v___x_46829__boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_602_);
lean_dec(v_sz_602_);
v___x_46829__boxed_614_ = lean_unbox_usize(v___x_603_);
lean_dec(v___x_603_);
v_res_615_ = l_Lean_Elab_wfRecursion___lam__0(v_a_601_, v_sz_boxed_613_, v___x_46829__boxed_614_, v___x_604_, v___x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v___x_605_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v___x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_options_627_; uint8_t v_hasTrace_628_; 
v_options_627_ = lean_ctor_get(v___y_624_, 2);
v_hasTrace_628_ = lean_ctor_get_uint8(v_options_627_, sizeof(void*)*1);
if (v_hasTrace_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v___x_619_);
v___x_629_ = lean_box(v_hasTrace_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_inheritedTraceOptions_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_inheritedTraceOptions_631_ = lean_ctor_get(v___y_624_, 13);
v___x_632_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
v___x_633_ = l_Lean_Name_append(v___x_632_, v___x_619_);
v___x_634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_631_, v_options_627_, v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = lean_box(v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v___x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Elab_wfRecursion___lam__1(v___x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v_snd_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_646_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_ref_655_; uint8_t v_kind_656_; lean_object* v_levelParams_657_; lean_object* v_modifiers_658_; lean_object* v_declName_659_; lean_object* v_binders_660_; lean_object* v_numSectionVars_661_; lean_object* v_type_662_; lean_object* v_value_663_; lean_object* v_termination_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref_known(v___x_654_, 1);
v_ref_655_ = lean_ctor_get(v_snd_646_, 0);
v_kind_656_ = lean_ctor_get_uint8(v_snd_646_, sizeof(void*)*9);
v_levelParams_657_ = lean_ctor_get(v_snd_646_, 1);
v_modifiers_658_ = lean_ctor_get(v_snd_646_, 2);
v_declName_659_ = lean_ctor_get(v_snd_646_, 3);
v_binders_660_ = lean_ctor_get(v_snd_646_, 4);
v_numSectionVars_661_ = lean_ctor_get(v_snd_646_, 5);
v_type_662_ = lean_ctor_get(v_snd_646_, 6);
v_value_663_ = lean_ctor_get(v_snd_646_, 7);
v_termination_664_ = lean_ctor_get(v_snd_646_, 8);
v_isSharedCheck_690_ = !lean_is_exclusive(v_snd_646_);
if (v_isSharedCheck_690_ == 0)
{
v___x_666_ = v_snd_646_;
v_isShared_667_ = v_isSharedCheck_690_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_termination_664_);
lean_inc(v_value_663_);
lean_inc(v_type_662_);
lean_inc(v_numSectionVars_661_);
lean_inc(v_binders_660_);
lean_inc(v_declName_659_);
lean_inc(v_modifiers_658_);
lean_inc(v_levelParams_657_);
lean_inc(v_ref_655_);
lean_dec(v_snd_646_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_690_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Elab_WF_preprocess(v_value_663_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_681_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_681_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_681_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_681_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_expr_673_; lean_object* v___x_675_; 
v_expr_673_ = lean_ctor_get(v_a_669_, 0);
lean_inc_ref(v_expr_673_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 7, v_expr_673_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_ref_655_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_levelParams_657_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_modifiers_658_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_declName_659_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_binders_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v_numSectionVars_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_type_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_expr_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_termination_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*9, v_kind_656_);
v___x_675_ = v_reuseFailAlloc_680_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_676_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_666_);
lean_dec_ref(v_termination_664_);
lean_dec_ref(v_type_662_);
lean_dec(v_numSectionVars_661_);
lean_dec(v_binders_660_);
lean_dec(v_declName_659_);
lean_dec_ref(v_modifiers_658_);
lean_dec(v_levelParams_657_);
lean_dec(v_ref_655_);
v_a_682_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_668_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_668_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_snd_646_);
v_a_691_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_654_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_654_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v_snd_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Elab_wfRecursion___lam__2(v_snd_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v___y_715_, uint8_t v_suppressElabErrors_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_x_717_, 0);
switch(lean_obj_tag(v_pre_718_))
{
case 1:
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_pre_718_, 0);
switch(lean_obj_tag(v_pre_719_))
{
case 0:
{
lean_object* v_str_720_; lean_object* v_str_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_str_720_ = lean_ctor_get(v_x_717_, 1);
v_str_721_ = lean_ctor_get(v_pre_718_, 1);
v___x_722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_723_ = lean_string_dec_eq(v_str_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_725_ = lean_string_dec_eq(v_str_721_, v___x_724_);
if (v___x_725_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_727_ = lean_string_dec_eq(v_str_720_, v___x_726_);
if (v___x_727_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_729_ = lean_string_dec_eq(v_str_720_, v___x_728_);
if (v___x_729_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
case 1:
{
lean_object* v_pre_730_; 
v_pre_730_ = lean_ctor_get(v_pre_719_, 0);
if (lean_obj_tag(v_pre_730_) == 0)
{
lean_object* v_str_731_; lean_object* v_str_732_; lean_object* v_str_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_str_731_ = lean_ctor_get(v_x_717_, 1);
v_str_732_ = lean_ctor_get(v_pre_718_, 1);
v_str_733_ = lean_ctor_get(v_pre_719_, 1);
v___x_734_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_735_ = lean_string_dec_eq(v_str_733_, v___x_734_);
if (v___x_735_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_737_ = lean_string_dec_eq(v_str_732_, v___x_736_);
if (v___x_737_ == 0)
{
return v___y_715_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_739_ = lean_string_dec_eq(v_str_731_, v___x_738_);
if (v___x_739_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
}
}
else
{
return v___y_715_;
}
}
default: 
{
return v___y_715_;
}
}
}
case 0:
{
lean_object* v_str_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_str_740_ = lean_ctor_get(v_x_717_, 1);
v___x_741_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__0));
v___x_742_ = lean_string_dec_eq(v_str_740_, v___x_741_);
if (v___x_742_ == 0)
{
return v___y_715_;
}
else
{
return v_suppressElabErrors_716_;
}
}
default: 
{
return v___y_715_;
}
}
}
else
{
return v___y_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v___y_743_, lean_object* v_suppressElabErrors_744_, lean_object* v_x_745_){
_start:
{
uint8_t v___y_47159__boxed_746_; uint8_t v_suppressElabErrors_boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v___y_47159__boxed_746_ = lean_unbox(v___y_743_);
v_suppressElabErrors_boxed_747_ = lean_unbox(v_suppressElabErrors_744_);
v_res_748_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v___y_47159__boxed_746_, v_suppressElabErrors_boxed_747_, v_x_745_);
lean_dec(v_x_745_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_751_, lean_object* v_msgData_752_, uint8_t v_severity_753_, uint8_t v_isSilent_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_797_; uint8_t v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v___y_804_; lean_object* v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; uint8_t v___y_839_; uint8_t v___x_844_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___y_850_; uint8_t v___y_851_; uint8_t v___y_852_; uint8_t v___y_854_; uint8_t v___x_869_; 
v___x_844_ = 2;
v___x_869_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_844_);
if (v___x_869_ == 0)
{
v___y_854_ = v___x_869_;
goto v___jp_853_;
}
else
{
uint8_t v___x_870_; 
lean_inc_ref(v_msgData_752_);
v___x_870_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_752_);
v___y_854_ = v___x_870_;
goto v___jp_853_;
}
v___jp_760_:
{
lean_object* v___x_770_; lean_object* v_currNamespace_771_; lean_object* v_openDecls_772_; lean_object* v_env_773_; lean_object* v_nextMacroScope_774_; lean_object* v_ngen_775_; lean_object* v_auxDeclNGen_776_; lean_object* v_traceState_777_; lean_object* v_cache_778_; lean_object* v_messages_779_; lean_object* v_infoState_780_; lean_object* v_snapshotTasks_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_795_; 
v___x_770_ = lean_st_ref_take(v___y_769_);
v_currNamespace_771_ = lean_ctor_get(v___y_768_, 6);
v_openDecls_772_ = lean_ctor_get(v___y_768_, 7);
v_env_773_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_774_ = lean_ctor_get(v___x_770_, 1);
v_ngen_775_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_776_ = lean_ctor_get(v___x_770_, 3);
v_traceState_777_ = lean_ctor_get(v___x_770_, 4);
v_cache_778_ = lean_ctor_get(v___x_770_, 5);
v_messages_779_ = lean_ctor_get(v___x_770_, 6);
v_infoState_780_ = lean_ctor_get(v___x_770_, 7);
v_snapshotTasks_781_ = lean_ctor_get(v___x_770_, 8);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_795_ == 0)
{
v___x_783_ = v___x_770_;
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snapshotTasks_781_);
lean_inc(v_infoState_780_);
lean_inc(v_messages_779_);
lean_inc(v_cache_778_);
lean_inc(v_traceState_777_);
lean_inc(v_auxDeclNGen_776_);
lean_inc(v_ngen_775_);
lean_inc(v_nextMacroScope_774_);
lean_inc(v_env_773_);
lean_dec(v___x_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v_openDecls_772_);
lean_inc(v_currNamespace_771_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_currNamespace_771_);
lean_ctor_set(v___x_785_, 1, v_openDecls_772_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___y_765_);
lean_inc_ref(v___y_763_);
lean_inc_ref(v___y_766_);
v___x_787_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_787_, 0, v___y_766_);
lean_ctor_set(v___x_787_, 1, v___y_767_);
lean_ctor_set(v___x_787_, 2, v___y_764_);
lean_ctor_set(v___x_787_, 3, v___y_763_);
lean_ctor_set(v___x_787_, 4, v___x_786_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5, v___y_761_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5 + 1, v___y_762_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*5 + 2, v_isSilent_754_);
v___x_788_ = l_Lean_MessageLog_add(v___x_787_, v_messages_779_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 6, v___x_788_);
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_env_773_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_nextMacroScope_774_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_ngen_775_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_auxDeclNGen_776_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_traceState_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 5, v_cache_778_);
lean_ctor_set(v_reuseFailAlloc_794_, 6, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 7, v_infoState_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 8, v_snapshotTasks_781_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_st_ref_set(v___y_769_, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
v___jp_796_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_820_; 
v___x_805_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_752_);
v___x_806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_805_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_820_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref_n(v___y_800_, 2);
v___x_811_ = l_Lean_FileMap_toPosition(v___y_800_, v___y_801_);
lean_dec(v___y_801_);
v___x_812_ = l_Lean_FileMap_toPosition(v___y_800_, v___y_804_);
lean_dec(v___y_804_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_803_ == 0)
{
lean_del_object(v___x_809_);
lean_dec_ref(v___y_797_);
v___y_761_ = v___y_798_;
v___y_762_ = v___y_799_;
v___y_763_ = v___x_814_;
v___y_764_ = v___x_813_;
v___y_765_ = v_a_807_;
v___y_766_ = v___y_802_;
v___y_767_ = v___x_811_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
else
{
uint8_t v___x_815_; 
lean_inc(v_a_807_);
v___x_815_ = l_Lean_MessageData_hasTag(v___y_797_, v_a_807_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec_ref_known(v___x_813_, 1);
lean_dec_ref(v___x_811_);
lean_dec(v_a_807_);
v___x_816_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_del_object(v___x_809_);
v___y_761_ = v___y_798_;
v___y_762_ = v___y_799_;
v___y_763_ = v___x_814_;
v___y_764_ = v___x_813_;
v___y_765_ = v_a_807_;
v___y_766_ = v___y_802_;
v___y_767_ = v___x_811_;
v___y_768_ = v___y_757_;
v___y_769_ = v___y_758_;
goto v___jp_760_;
}
}
}
}
v___jp_821_:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Syntax_getTailPos_x3f(v___y_828_, v___y_823_);
lean_dec(v___y_828_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_inc(v___y_829_);
v___y_797_ = v___y_822_;
v___y_798_ = v___y_823_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_824_;
v___y_801_ = v___y_829_;
v___y_802_ = v___y_826_;
v___y_803_ = v___y_827_;
v___y_804_ = v___y_829_;
goto v___jp_796_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_830_, 1);
v___y_797_ = v___y_822_;
v___y_798_ = v___y_823_;
v___y_799_ = v___y_825_;
v___y_800_ = v___y_824_;
v___y_801_ = v___y_829_;
v___y_802_ = v___y_826_;
v___y_803_ = v___y_827_;
v___y_804_ = v_val_831_;
goto v___jp_796_;
}
}
v___jp_832_:
{
lean_object* v_ref_840_; lean_object* v___x_841_; 
v_ref_840_ = l_Lean_replaceRef(v_ref_751_, v___y_834_);
v___x_841_ = l_Lean_Syntax_getPos_x3f(v_ref_840_, v___y_835_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___y_822_ = v___y_833_;
v___y_823_ = v___y_835_;
v___y_824_ = v___y_836_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_837_;
v___y_827_ = v___y_838_;
v___y_828_ = v_ref_840_;
v___y_829_ = v___x_842_;
goto v___jp_821_;
}
else
{
lean_object* v_val_843_; 
v_val_843_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_841_, 1);
v___y_822_ = v___y_833_;
v___y_823_ = v___y_835_;
v___y_824_ = v___y_836_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_837_;
v___y_827_ = v___y_838_;
v___y_828_ = v_ref_840_;
v___y_829_ = v_val_843_;
goto v___jp_821_;
}
}
v___jp_845_:
{
if (v___y_852_ == 0)
{
v___y_833_ = v___y_848_;
v___y_834_ = v___y_846_;
v___y_835_ = v___y_851_;
v___y_836_ = v___y_847_;
v___y_837_ = v___y_849_;
v___y_838_ = v___y_850_;
v___y_839_ = v_severity_753_;
goto v___jp_832_;
}
else
{
v___y_833_ = v___y_848_;
v___y_834_ = v___y_846_;
v___y_835_ = v___y_851_;
v___y_836_ = v___y_847_;
v___y_837_ = v___y_849_;
v___y_838_ = v___y_850_;
v___y_839_ = v___x_844_;
goto v___jp_832_;
}
}
v___jp_853_:
{
if (v___y_854_ == 0)
{
lean_object* v_fileName_855_; lean_object* v_fileMap_856_; lean_object* v_options_857_; lean_object* v_ref_858_; uint8_t v_suppressElabErrors_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___f_862_; uint8_t v___x_863_; uint8_t v___x_864_; 
v_fileName_855_ = lean_ctor_get(v___y_757_, 0);
v_fileMap_856_ = lean_ctor_get(v___y_757_, 1);
v_options_857_ = lean_ctor_get(v___y_757_, 2);
v_ref_858_ = lean_ctor_get(v___y_757_, 5);
v_suppressElabErrors_859_ = lean_ctor_get_uint8(v___y_757_, sizeof(void*)*14 + 1);
v___x_860_ = lean_box(v___y_854_);
v___x_861_ = lean_box(v_suppressElabErrors_859_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_862_, 0, v___x_860_);
lean_closure_set(v___f_862_, 1, v___x_861_);
v___x_863_ = 1;
v___x_864_ = l_Lean_instBEqMessageSeverity_beq(v_severity_753_, v___x_863_);
if (v___x_864_ == 0)
{
v___y_846_ = v_ref_858_;
v___y_847_ = v_fileMap_856_;
v___y_848_ = v___f_862_;
v___y_849_ = v_fileName_855_;
v___y_850_ = v_suppressElabErrors_859_;
v___y_851_ = v___y_854_;
v___y_852_ = v___x_864_;
goto v___jp_845_;
}
else
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = l_Lean_warningAsError;
v___x_866_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_857_, v___x_865_);
v___y_846_ = v_ref_858_;
v___y_847_ = v_fileMap_856_;
v___y_848_ = v___f_862_;
v___y_849_ = v_fileName_855_;
v___y_850_ = v_suppressElabErrors_859_;
v___y_851_ = v___y_854_;
v___y_852_ = v___x_866_;
goto v___jp_845_;
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_msgData_752_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_871_, lean_object* v_msgData_872_, lean_object* v_severity_873_, lean_object* v_isSilent_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_severity_boxed_880_; uint8_t v_isSilent_boxed_881_; lean_object* v_res_882_; 
v_severity_boxed_880_ = lean_unbox(v_severity_873_);
v_isSilent_boxed_881_ = lean_unbox(v_isSilent_874_);
v_res_882_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_871_, v_msgData_872_, v_severity_boxed_880_, v_isSilent_boxed_881_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v_ref_871_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_883_, lean_object* v_msgData_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = 1;
v___x_893_ = 0;
v___x_894_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_883_, v_msgData_884_, v___x_892_, v___x_893_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_895_, lean_object* v_msgData_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_895_, v_msgData_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v_ref_895_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v_as_913_, size_t v_i_914_, size_t v_stop_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_a_925_; uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_eq(v_i_914_, v_stop_915_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v_name_931_; lean_object* v_stx_932_; uint8_t v___y_934_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_930_ = lean_array_uget_borrowed(v_as_913_, v_i_914_);
v_name_931_ = lean_ctor_get(v___x_930_, 0);
v_stx_932_ = lean_ctor_get(v___x_930_, 1);
v___x_944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_945_ = lean_name_eq(v_name_931_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_947_ = lean_name_eq(v_name_931_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_box(0);
v_a_925_ = v___x_948_;
goto v___jp_924_;
}
else
{
v___y_934_ = v___x_947_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_945_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_931_);
v___x_936_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_931_, v___y_934_);
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
v___x_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
v___x_941_ = l_Lean_MessageData_ofFormat(v___x_940_);
v___x_942_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_932_, v___x_941_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_a_925_ = v_a_943_;
goto v___jp_924_;
}
else
{
return v___x_942_;
}
}
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_916_);
return v___x_949_;
}
v___jp_924_:
{
size_t v___x_926_; size_t v___x_927_; 
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_914_, v___x_926_);
v_i_914_ = v___x_927_;
v_b_916_ = v_a_925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v_as_950_, lean_object* v_i_951_, lean_object* v_stop_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
size_t v_i_boxed_961_; size_t v_stop_boxed_962_; lean_object* v_res_963_; 
v_i_boxed_961_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_stop_boxed_962_ = lean_unbox_usize(v_stop_952_);
lean_dec(v_stop_952_);
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_as_950_, v_i_boxed_961_, v_stop_boxed_962_, v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
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
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_986_, v___x_992_, v___x_993_, v___x_989_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
v___y_981_ = v___x_994_;
goto v___jp_980_;
}
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((size_t)0ULL);
v___x_996_ = lean_usize_of_nat(v___x_988_);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_986_, v___x_995_, v___x_996_, v___x_989_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v_as_999_, lean_object* v_i_1000_, lean_object* v_stop_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
size_t v_i_boxed_1010_; size_t v_stop_boxed_1011_; lean_object* v_res_1012_; 
v_i_boxed_1010_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_stop_boxed_1011_ = lean_unbox_usize(v_stop_1001_);
lean_dec(v_stop_1001_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_as_999_, v_i_boxed_1010_, v_stop_boxed_1011_, v_b_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec_ref(v_as_999_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_bs_1015_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1016_ == 0)
{
return v_bs_1015_;
}
else
{
lean_object* v_v_1017_; lean_object* v_termination_1018_; lean_object* v_decreasingBy_x3f_1019_; lean_object* v___x_1020_; lean_object* v_bs_x27_1021_; size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v_v_1017_ = lean_array_uget_borrowed(v_bs_1015_, v_i_1014_);
v_termination_1018_ = lean_ctor_get(v_v_1017_, 8);
v_decreasingBy_x3f_1019_ = lean_ctor_get(v_termination_1018_, 4);
lean_inc(v_decreasingBy_x3f_1019_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v_bs_x27_1021_ = lean_array_uset(v_bs_1015_, v_i_1014_, v___x_1020_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1014_, v___x_1022_);
v___x_1024_ = lean_array_uset(v_bs_x27_1021_, v_i_1014_, v_decreasingBy_x3f_1019_);
v_i_1014_ = v___x_1023_;
v_bs_1015_ = v___x_1024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1026_, lean_object* v_i_1027_, lean_object* v_bs_1028_){
_start:
{
size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1026_);
lean_dec(v_sz_1026_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1029_, v_i_boxed_1030_, v_bs_1028_);
return v_res_1031_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1032_; double v___x_1033_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_float_of_nat(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1036_, lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_ref_1043_; lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1089_; 
v_ref_1043_ = lean_ctor_get(v___y_1040_, 5);
v___x_1044_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1089_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1089_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_traceState_1050_; lean_object* v_env_1051_; lean_object* v_nextMacroScope_1052_; lean_object* v_ngen_1053_; lean_object* v_auxDeclNGen_1054_; lean_object* v_cache_1055_; lean_object* v_messages_1056_; lean_object* v_infoState_1057_; lean_object* v_snapshotTasks_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1088_; 
v___x_1049_ = lean_st_ref_take(v___y_1041_);
v_traceState_1050_ = lean_ctor_get(v___x_1049_, 4);
v_env_1051_ = lean_ctor_get(v___x_1049_, 0);
v_nextMacroScope_1052_ = lean_ctor_get(v___x_1049_, 1);
v_ngen_1053_ = lean_ctor_get(v___x_1049_, 2);
v_auxDeclNGen_1054_ = lean_ctor_get(v___x_1049_, 3);
v_cache_1055_ = lean_ctor_get(v___x_1049_, 5);
v_messages_1056_ = lean_ctor_get(v___x_1049_, 6);
v_infoState_1057_ = lean_ctor_get(v___x_1049_, 7);
v_snapshotTasks_1058_ = lean_ctor_get(v___x_1049_, 8);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1088_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snapshotTasks_1058_);
lean_inc(v_infoState_1057_);
lean_inc(v_messages_1056_);
lean_inc(v_cache_1055_);
lean_inc(v_traceState_1050_);
lean_inc(v_auxDeclNGen_1054_);
lean_inc(v_ngen_1053_);
lean_inc(v_nextMacroScope_1052_);
lean_inc(v_env_1051_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1088_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
uint64_t v_tid_1062_; lean_object* v_traces_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1087_; 
v_tid_1062_ = lean_ctor_get_uint64(v_traceState_1050_, sizeof(void*)*1);
v_traces_1063_ = lean_ctor_get(v_traceState_1050_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_traceState_1050_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1065_ = v_traceState_1050_;
v_isShared_1066_ = v_isSharedCheck_1087_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_traces_1063_);
lean_dec(v_traceState_1050_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1087_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; double v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1069_ = 0;
v___x_1070_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1071_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1071_, 0, v_cls_1036_);
lean_ctor_set(v___x_1071_, 1, v___x_1067_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
lean_ctor_set_float(v___x_1071_, sizeof(void*)*3, v___x_1068_);
lean_ctor_set_float(v___x_1071_, sizeof(void*)*3 + 8, v___x_1068_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*3 + 16, v___x_1069_);
v___x_1072_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1073_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v_a_1045_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
lean_inc(v_ref_1043_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_ref_1043_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_PersistentArray_push___redArg(v_traces_1063_, v___x_1074_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1075_);
v___x_1077_ = v___x_1065_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1075_);
lean_ctor_set_uint64(v_reuseFailAlloc_1086_, sizeof(void*)*1, v_tid_1062_);
v___x_1077_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 4, v___x_1077_);
v___x_1079_ = v___x_1060_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_env_1051_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_nextMacroScope_1052_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_ngen_1053_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_auxDeclNGen_1054_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1085_, 5, v_cache_1055_);
lean_ctor_set(v_reuseFailAlloc_1085_, 6, v_messages_1056_);
lean_ctor_set(v_reuseFailAlloc_1085_, 7, v_infoState_1057_);
lean_ctor_set(v_reuseFailAlloc_1085_, 8, v_snapshotTasks_1058_);
v___x_1079_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_st_ref_set(v___y_1041_, v___x_1079_);
v___x_1081_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1081_);
v___x_1083_ = v___x_1047_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1090_, lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1090_, v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1101_, lean_object* v_snd_1102_, size_t v_sz_1103_, size_t v___x_1104_, lean_object* v_a_1105_, lean_object* v_fixedArgs_1106_, lean_object* v_fst_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v_wfRel_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v_a_1127_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v_options_1276_; uint8_t v_hasTrace_1277_; 
v_options_1276_ = lean_ctor_get(v___y_1116_, 2);
v_hasTrace_1277_ = lean_ctor_get_uint8(v_options_1276_, sizeof(void*)*1);
if (v_hasTrace_1277_ == 0)
{
lean_dec(v___x_1110_);
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
goto v___jp_1251_;
}
else
{
lean_object* v_inheritedTraceOptions_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_inheritedTraceOptions_1278_ = lean_ctor_get(v___y_1116_, 13);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
lean_inc(v___x_1110_);
v___x_1280_ = l_Lean_Name_append(v___x_1279_, v___x_1110_);
v___x_1281_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1278_, v_options_1276_, v___x_1280_);
lean_dec(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1110_);
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1111_);
v___x_1283_ = l_Lean_MessageData_ofExpr(v_wfRel_1111_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1110_, v___x_1284_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref_known(v___x_1285_, 1);
v___y_1252_ = v___y_1112_;
v___y_1253_ = v___y_1113_;
v___y_1254_ = v___y_1114_;
v___y_1255_ = v___y_1115_;
v___y_1256_ = v___y_1116_;
v___y_1257_ = v___y_1117_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_wfRel_1111_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v_fixedArgs_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_fst_1101_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
v___jp_1119_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v___x_1128_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1123_, v___y_1122_, v___y_1124_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1128_, 0);
lean_dec(v_unused_1136_);
v___x_1130_ = v___x_1128_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v___x_1128_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 1);
lean_ctor_set(v___x_1130_, 0, v_a_1127_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1127_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
v___jp_1137_:
{
if (lean_obj_tag(v___y_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_env_1149_; lean_object* v___x_1150_; 
v_a_1146_ = lean_ctor_get(v___y_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___y_1145_, 1);
v___x_1147_ = lean_st_ref_get(v___y_1142_);
v___x_1148_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1141_, v___y_1140_, v___y_1142_);
lean_dec_ref(v___x_1148_);
v_env_1149_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref_n(v_env_1149_, 2);
lean_dec(v___x_1147_);
v___x_1150_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1149_, v_a_1146_, v___y_1144_, v___y_1142_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1210_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1210_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1210_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v_env_1156_; lean_object* v_nextMacroScope_1157_; lean_object* v_ngen_1158_; lean_object* v_auxDeclNGen_1159_; lean_object* v_traceState_1160_; lean_object* v_messages_1161_; lean_object* v_infoState_1162_; lean_object* v_snapshotTasks_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1208_; 
v___x_1155_ = lean_st_ref_take(v___y_1142_);
v_env_1156_ = lean_ctor_get(v___x_1155_, 0);
v_nextMacroScope_1157_ = lean_ctor_get(v___x_1155_, 1);
v_ngen_1158_ = lean_ctor_get(v___x_1155_, 2);
v_auxDeclNGen_1159_ = lean_ctor_get(v___x_1155_, 3);
v_traceState_1160_ = lean_ctor_get(v___x_1155_, 4);
v_messages_1161_ = lean_ctor_get(v___x_1155_, 6);
v_infoState_1162_ = lean_ctor_get(v___x_1155_, 7);
v_snapshotTasks_1163_ = lean_ctor_get(v___x_1155_, 8);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1155_, 5);
lean_dec(v_unused_1209_);
v___x_1165_ = v___x_1155_;
v_isShared_1166_ = v_isSharedCheck_1208_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snapshotTasks_1163_);
lean_inc(v_infoState_1162_);
lean_inc(v_messages_1161_);
lean_inc(v_traceState_1160_);
lean_inc(v_auxDeclNGen_1159_);
lean_inc(v_ngen_1158_);
lean_inc(v_nextMacroScope_1157_);
lean_inc(v_env_1156_);
lean_dec(v___x_1155_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1208_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = l_Lean_copyExtraModUses(v_env_1149_, v_env_1156_);
v___x_1168_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 5, v___x_1168_);
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_nextMacroScope_1157_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_ngen_1158_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_auxDeclNGen_1159_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_traceState_1160_);
lean_ctor_set(v_reuseFailAlloc_1207_, 5, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1207_, 6, v_messages_1161_);
lean_ctor_set(v_reuseFailAlloc_1207_, 7, v_infoState_1162_);
lean_ctor_set(v_reuseFailAlloc_1207_, 8, v_snapshotTasks_1163_);
v___x_1170_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_mctx_1173_; lean_object* v_zetaDeltaFVarIds_1174_; lean_object* v_postponed_1175_; lean_object* v_diag_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1205_; 
v___x_1171_ = lean_st_ref_set(v___y_1142_, v___x_1170_);
v___x_1172_ = lean_st_ref_take(v___y_1140_);
v_mctx_1173_ = lean_ctor_get(v___x_1172_, 0);
v_zetaDeltaFVarIds_1174_ = lean_ctor_get(v___x_1172_, 2);
v_postponed_1175_ = lean_ctor_get(v___x_1172_, 3);
v_diag_1176_ = lean_ctor_get(v___x_1172_, 4);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1172_, 1);
lean_dec(v_unused_1206_);
v___x_1178_ = v___x_1172_;
v_isShared_1179_ = v_isSharedCheck_1205_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_diag_1176_);
lean_inc(v_postponed_1175_);
lean_inc(v_zetaDeltaFVarIds_1174_);
lean_inc(v_mctx_1173_);
lean_dec(v___x_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1205_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_mctx_1173_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_zetaDeltaFVarIds_1174_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_postponed_1175_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_diag_1176_);
v___x_1182_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v_ref_1184_; uint8_t v_kind_1185_; lean_object* v_levelParams_1186_; lean_object* v_modifiers_1187_; lean_object* v_declName_1188_; lean_object* v_binders_1189_; lean_object* v_numSectionVars_1190_; lean_object* v_type_1191_; lean_object* v_termination_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v___x_1183_ = lean_st_ref_set(v___y_1140_, v___x_1182_);
v_ref_1184_ = lean_ctor_get(v_fst_1101_, 0);
v_kind_1185_ = lean_ctor_get_uint8(v_fst_1101_, sizeof(void*)*9);
v_levelParams_1186_ = lean_ctor_get(v_fst_1101_, 1);
v_modifiers_1187_ = lean_ctor_get(v_fst_1101_, 2);
v_declName_1188_ = lean_ctor_get(v_fst_1101_, 3);
v_binders_1189_ = lean_ctor_get(v_fst_1101_, 4);
v_numSectionVars_1190_ = lean_ctor_get(v_fst_1101_, 5);
v_type_1191_ = lean_ctor_get(v_fst_1101_, 6);
v_termination_1192_ = lean_ctor_get(v_fst_1101_, 8);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_fst_1101_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_fst_1101_, 7);
lean_dec(v_unused_1203_);
v___x_1194_ = v_fst_1101_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_termination_1192_);
lean_inc(v_type_1191_);
lean_inc(v_numSectionVars_1190_);
lean_inc(v_binders_1189_);
lean_inc(v_declName_1188_);
lean_inc(v_modifiers_1187_);
lean_inc(v_levelParams_1186_);
lean_inc(v_ref_1184_);
lean_dec(v_fst_1101_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 7, v_a_1151_);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_ref_1184_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_levelParams_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_modifiers_1187_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_declName_1188_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_binders_1189_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v_numSectionVars_1190_);
lean_ctor_set(v_reuseFailAlloc_1201_, 6, v_type_1191_);
lean_ctor_set(v_reuseFailAlloc_1201_, 7, v_a_1151_);
lean_ctor_set(v_reuseFailAlloc_1201_, 8, v_termination_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1201_, sizeof(void*)*9, v_kind_1185_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1197_);
v___x_1199_ = v___x_1153_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
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
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_env_1149_);
lean_dec_ref(v_fst_1101_);
v_a_1211_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1150_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1150_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; 
lean_dec_ref(v_fst_1101_);
v_a_1219_ = lean_ctor_get(v___y_1145_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___y_1145_, 1);
v___y_1120_ = v___y_1138_;
v___y_1121_ = v___y_1139_;
v___y_1122_ = v___y_1140_;
v___y_1123_ = v___y_1141_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v_a_1127_ = v_a_1219_;
goto v___jp_1119_;
}
}
v___jp_1220_:
{
lean_object* v___x_1227_; lean_object* v_env_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_get(v___y_1226_);
v_env_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc_ref(v_env_1228_);
lean_dec(v___x_1227_);
v___x_1229_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1102_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1229_, 1);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1103_, v___x_1104_, v_a_1105_);
lean_inc_ref(v_fst_1101_);
v___x_1231_ = l_Lean_Elab_WF_mkFix(v_fst_1101_, v_fixedArgs_1106_, v_fst_1107_, v_wfRel_1111_, v___x_1108_, v___x_1230_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1233_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1232_, v___y_1225_, v___y_1226_);
v___y_1138_ = v___y_1221_;
v___y_1139_ = v___y_1222_;
v___y_1140_ = v___y_1224_;
v___y_1141_ = v_env_1228_;
v___y_1142_ = v___y_1226_;
v___y_1143_ = v___y_1223_;
v___y_1144_ = v___y_1225_;
v___y_1145_ = v___x_1233_;
goto v___jp_1137_;
}
else
{
v___y_1138_ = v___y_1221_;
v___y_1139_ = v___y_1222_;
v___y_1140_ = v___y_1224_;
v___y_1141_ = v_env_1228_;
v___y_1142_ = v___y_1226_;
v___y_1143_ = v___y_1223_;
v___y_1144_ = v___y_1225_;
v___y_1145_ = v___x_1231_;
goto v___jp_1137_;
}
}
else
{
lean_object* v_a_1234_; 
lean_dec_ref(v_wfRel_1111_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v_fixedArgs_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_fst_1101_);
v_a_1234_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1229_, 1);
v___y_1120_ = v___y_1221_;
v___y_1121_ = v___y_1222_;
v___y_1122_ = v___y_1224_;
v___y_1123_ = v_env_1228_;
v___y_1124_ = v___y_1226_;
v___y_1125_ = v___y_1223_;
v___y_1126_ = v___y_1225_;
v_a_1127_ = v_a_1234_;
goto v___jp_1119_;
}
}
v___jp_1235_:
{
if (lean_obj_tag(v___y_1242_) == 0)
{
lean_dec_ref_known(v___y_1242_, 1);
v___y_1221_ = v___y_1237_;
v___y_1222_ = v___y_1239_;
v___y_1223_ = v___y_1241_;
v___y_1224_ = v___y_1240_;
v___y_1225_ = v___y_1236_;
v___y_1226_ = v___y_1238_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_wfRel_1111_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v_fixedArgs_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_fst_1101_);
v_a_1243_ = lean_ctor_get(v___y_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___y_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___y_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___y_1242_);
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
v___jp_1251_:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_wfRel_1111_);
v___x_1258_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1111_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
if (lean_obj_tag(v_a_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_array_get_size(v_a_1105_);
v___x_1262_ = lean_nat_dec_lt(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
goto v___jp_1220_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_le(v___x_1261_, v___x_1261_);
if (v___x_1263_ == 0)
{
if (v___x_1262_ == 0)
{
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
goto v___jp_1220_;
}
else
{
size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_usize_of_nat(v___x_1261_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1105_, v___x_1104_, v___x_1264_, v___x_1109_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
v___y_1236_ = v___y_1256_;
v___y_1237_ = v___y_1252_;
v___y_1238_ = v___y_1257_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1255_;
v___y_1241_ = v___y_1254_;
v___y_1242_ = v___x_1265_;
goto v___jp_1235_;
}
}
else
{
size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_usize_of_nat(v___x_1261_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_1105_, v___x_1104_, v___x_1266_, v___x_1109_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
v___y_1236_ = v___y_1256_;
v___y_1237_ = v___y_1252_;
v___y_1238_ = v___y_1257_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1255_;
v___y_1241_ = v___y_1254_;
v___y_1242_ = v___x_1267_;
goto v___jp_1235_;
}
}
}
else
{
lean_dec_ref_known(v_a_1259_, 1);
v___y_1221_ = v___y_1252_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___y_1256_;
v___y_1226_ = v___y_1257_;
goto v___jp_1220_;
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_wfRel_1111_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v_fixedArgs_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_fst_1101_);
v_a_1268_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1258_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1294_ = _args[0];
lean_object* v_snd_1295_ = _args[1];
lean_object* v_sz_1296_ = _args[2];
lean_object* v___x_1297_ = _args[3];
lean_object* v_a_1298_ = _args[4];
lean_object* v_fixedArgs_1299_ = _args[5];
lean_object* v_fst_1300_ = _args[6];
lean_object* v___x_1301_ = _args[7];
lean_object* v___x_1302_ = _args[8];
lean_object* v___x_1303_ = _args[9];
lean_object* v_wfRel_1304_ = _args[10];
lean_object* v___y_1305_ = _args[11];
lean_object* v___y_1306_ = _args[12];
lean_object* v___y_1307_ = _args[13];
lean_object* v___y_1308_ = _args[14];
lean_object* v___y_1309_ = _args[15];
lean_object* v___y_1310_ = _args[16];
lean_object* v___y_1311_ = _args[17];
_start:
{
size_t v_sz_boxed_1312_; size_t v___x_47759__boxed_1313_; lean_object* v_res_1314_; 
v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v___x_47759__boxed_1313_ = lean_unbox_usize(v___x_1297_);
lean_dec(v___x_1297_);
v_res_1314_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1294_, v_snd_1295_, v_sz_boxed_1312_, v___x_47759__boxed_1313_, v_a_1298_, v_fixedArgs_1299_, v_fst_1300_, v___x_1301_, v___x_1302_, v___x_1303_, v_wfRel_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_snd_1295_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1318_, size_t v___x_1319_, lean_object* v_a_1320_, lean_object* v_fst_1321_, lean_object* v_snd_1322_, lean_object* v_fst_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v_declName_1326_, lean_object* v_fst_1327_, lean_object* v_wf_1328_, lean_object* v_fixedArgs_1329_, lean_object* v_type_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_whnfForall(v_type_1330_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___x_1353_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1353_ = l_Lean_Expr_isForall(v_a_1339_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_fixedArgs_1329_);
lean_dec_ref(v_wf_1328_);
lean_dec_ref(v_fst_1327_);
lean_dec(v_declName_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v_fst_1323_);
lean_dec_ref(v_snd_1322_);
lean_dec_ref(v_fst_1321_);
lean_dec_ref(v_a_1320_);
v___x_1354_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1355_ = l_Lean_MessageData_ofExpr(v_a_1339_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1356_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
v___y_1341_ = v___y_1331_;
v___y_1342_ = v___y_1332_;
v___y_1343_ = v___y_1333_;
v___y_1344_ = v___y_1334_;
v___y_1345_ = v___y_1335_;
v___y_1346_ = v___y_1336_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___x_1347_ = l_Lean_Expr_bindingDomain_x21(v_a_1339_);
lean_dec(v_a_1339_);
lean_inc_ref(v_a_1320_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1318_, v___x_1319_, v_a_1320_);
v___x_1349_ = lean_box_usize(v_sz_1318_);
v___x_1350_ = lean_box_usize(v___x_1319_);
lean_inc_ref(v___x_1348_);
lean_inc_ref(v_fst_1323_);
lean_inc_ref(v_fixedArgs_1329_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1351_, 0, v_fst_1321_);
lean_closure_set(v___f_1351_, 1, v_snd_1322_);
lean_closure_set(v___f_1351_, 2, v___x_1349_);
lean_closure_set(v___f_1351_, 3, v___x_1350_);
lean_closure_set(v___f_1351_, 4, v_a_1320_);
lean_closure_set(v___f_1351_, 5, v_fixedArgs_1329_);
lean_closure_set(v___f_1351_, 6, v_fst_1323_);
lean_closure_set(v___f_1351_, 7, v___x_1348_);
lean_closure_set(v___f_1351_, 8, v___x_1324_);
lean_closure_set(v___f_1351_, 9, v___x_1325_);
v___x_1352_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1348_, v_declName_1326_, v_fst_1327_, v_fixedArgs_1329_, v_fst_1323_, v___x_1347_, v_wf_1328_, v___f_1351_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1352_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v_fixedArgs_1329_);
lean_dec_ref(v_wf_1328_);
lean_dec_ref(v_fst_1327_);
lean_dec(v_declName_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v_fst_1323_);
lean_dec_ref(v_snd_1322_);
lean_dec_ref(v_fst_1321_);
lean_dec_ref(v_a_1320_);
v_a_1366_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1338_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1338_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1374_ = _args[0];
lean_object* v___x_1375_ = _args[1];
lean_object* v_a_1376_ = _args[2];
lean_object* v_fst_1377_ = _args[3];
lean_object* v_snd_1378_ = _args[4];
lean_object* v_fst_1379_ = _args[5];
lean_object* v___x_1380_ = _args[6];
lean_object* v___x_1381_ = _args[7];
lean_object* v_declName_1382_ = _args[8];
lean_object* v_fst_1383_ = _args[9];
lean_object* v_wf_1384_ = _args[10];
lean_object* v_fixedArgs_1385_ = _args[11];
lean_object* v_type_1386_ = _args[12];
lean_object* v___y_1387_ = _args[13];
lean_object* v___y_1388_ = _args[14];
lean_object* v___y_1389_ = _args[15];
lean_object* v___y_1390_ = _args[16];
lean_object* v___y_1391_ = _args[17];
lean_object* v___y_1392_ = _args[18];
lean_object* v___y_1393_ = _args[19];
_start:
{
size_t v_sz_boxed_1394_; size_t v___x_48117__boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1374_);
lean_dec(v_sz_1374_);
v___x_48117__boxed_1395_ = lean_unbox_usize(v___x_1375_);
lean_dec(v___x_1375_);
v_res_1396_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1394_, v___x_48117__boxed_1395_, v_a_1376_, v_fst_1377_, v_snd_1378_, v_fst_1379_, v___x_1380_, v___x_1381_, v_declName_1382_, v_fst_1383_, v_wf_1384_, v_fixedArgs_1385_, v_type_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1397_, lean_object* v_fst_1398_, lean_object* v_fst_1399_, lean_object* v_fst_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Elab_WF_guessLex(v_a_1397_, v_fst_1398_, v_fst_1399_, v_fst_1400_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1409_, lean_object* v_fst_1410_, lean_object* v_fst_1411_, lean_object* v_fst_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1409_, v_fst_1410_, v_fst_1411_, v_fst_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1421_, uint8_t v_isExporting_1422_, lean_object* v___x_1423_, lean_object* v___y_1424_, lean_object* v___x_1425_, lean_object* v_a_x3f_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v_env_1429_; lean_object* v_nextMacroScope_1430_; lean_object* v_ngen_1431_; lean_object* v_auxDeclNGen_1432_; lean_object* v_traceState_1433_; lean_object* v_messages_1434_; lean_object* v_infoState_1435_; lean_object* v_snapshotTasks_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1461_; 
v___x_1428_ = lean_st_ref_take(v___y_1421_);
v_env_1429_ = lean_ctor_get(v___x_1428_, 0);
v_nextMacroScope_1430_ = lean_ctor_get(v___x_1428_, 1);
v_ngen_1431_ = lean_ctor_get(v___x_1428_, 2);
v_auxDeclNGen_1432_ = lean_ctor_get(v___x_1428_, 3);
v_traceState_1433_ = lean_ctor_get(v___x_1428_, 4);
v_messages_1434_ = lean_ctor_get(v___x_1428_, 6);
v_infoState_1435_ = lean_ctor_get(v___x_1428_, 7);
v_snapshotTasks_1436_ = lean_ctor_get(v___x_1428_, 8);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1428_, 5);
lean_dec(v_unused_1462_);
v___x_1438_ = v___x_1428_;
v_isShared_1439_ = v_isSharedCheck_1461_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_snapshotTasks_1436_);
lean_inc(v_infoState_1435_);
lean_inc(v_messages_1434_);
lean_inc(v_traceState_1433_);
lean_inc(v_auxDeclNGen_1432_);
lean_inc(v_ngen_1431_);
lean_inc(v_nextMacroScope_1430_);
lean_inc(v_env_1429_);
lean_dec(v___x_1428_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1461_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = l_Lean_Environment_setExporting(v_env_1429_, v_isExporting_1422_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 5, v___x_1423_);
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_nextMacroScope_1430_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_ngen_1431_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_auxDeclNGen_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_traceState_1433_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_messages_1434_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_infoState_1435_);
lean_ctor_set(v_reuseFailAlloc_1460_, 8, v_snapshotTasks_1436_);
v___x_1442_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_mctx_1445_; lean_object* v_zetaDeltaFVarIds_1446_; lean_object* v_postponed_1447_; lean_object* v_diag_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v___x_1443_ = lean_st_ref_set(v___y_1421_, v___x_1442_);
v___x_1444_ = lean_st_ref_take(v___y_1424_);
v_mctx_1445_ = lean_ctor_get(v___x_1444_, 0);
v_zetaDeltaFVarIds_1446_ = lean_ctor_get(v___x_1444_, 2);
v_postponed_1447_ = lean_ctor_get(v___x_1444_, 3);
v_diag_1448_ = lean_ctor_get(v___x_1444_, 4);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1444_, 1);
lean_dec(v_unused_1459_);
v___x_1450_ = v___x_1444_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_diag_1448_);
lean_inc(v_postponed_1447_);
lean_inc(v_zetaDeltaFVarIds_1446_);
lean_inc(v_mctx_1445_);
lean_dec(v___x_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___x_1425_);
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_mctx_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_zetaDeltaFVarIds_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_postponed_1447_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_diag_1448_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_st_ref_set(v___y_1424_, v___x_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1463_, lean_object* v_isExporting_1464_, lean_object* v___x_1465_, lean_object* v___y_1466_, lean_object* v___x_1467_, lean_object* v_a_x3f_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_isExporting_boxed_1470_; lean_object* v_res_1471_; 
v_isExporting_boxed_1470_ = lean_unbox(v_isExporting_1464_);
v_res_1471_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1463_, v_isExporting_boxed_1470_, v___x_1465_, v___y_1466_, v___x_1467_, v_a_x3f_1468_);
lean_dec(v_a_x3f_1468_);
lean_dec(v___y_1466_);
lean_dec(v___y_1463_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1472_, uint8_t v_isExporting_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; lean_object* v_env_1482_; uint8_t v_isExporting_1483_; uint8_t v___y_1550_; lean_object* v___x_1552_; uint8_t v_isModule_1553_; uint8_t v___x_1554_; 
v___x_1481_ = lean_st_ref_get(v___y_1479_);
v_env_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_env_1482_);
lean_dec(v___x_1481_);
v_isExporting_1483_ = lean_ctor_get_uint8(v_env_1482_, sizeof(void*)*8);
v___x_1552_ = l_Lean_Environment_header(v_env_1482_);
lean_dec_ref(v_env_1482_);
v_isModule_1553_ = lean_ctor_get_uint8(v___x_1552_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1552_);
v___x_1554_ = lean_bool_not(v_isModule_1553_);
if (v___x_1554_ == 0)
{
if (v_isExporting_1483_ == 0)
{
if (v_isExporting_1473_ == 0)
{
lean_object* v___x_1555_; 
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
v___x_1555_ = lean_apply_7(v_x_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
return v___x_1555_;
}
else
{
goto v___jp_1484_;
}
}
else
{
v___y_1550_ = v_isExporting_1473_;
goto v___jp_1549_;
}
}
else
{
v___y_1550_ = v___x_1554_;
goto v___jp_1549_;
}
v___jp_1484_:
{
lean_object* v___x_1485_; lean_object* v_env_1486_; lean_object* v_nextMacroScope_1487_; lean_object* v_ngen_1488_; lean_object* v_auxDeclNGen_1489_; lean_object* v_traceState_1490_; lean_object* v_messages_1491_; lean_object* v_infoState_1492_; lean_object* v_snapshotTasks_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1547_; 
v___x_1485_ = lean_st_ref_take(v___y_1479_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
v_nextMacroScope_1487_ = lean_ctor_get(v___x_1485_, 1);
v_ngen_1488_ = lean_ctor_get(v___x_1485_, 2);
v_auxDeclNGen_1489_ = lean_ctor_get(v___x_1485_, 3);
v_traceState_1490_ = lean_ctor_get(v___x_1485_, 4);
v_messages_1491_ = lean_ctor_get(v___x_1485_, 6);
v_infoState_1492_ = lean_ctor_get(v___x_1485_, 7);
v_snapshotTasks_1493_ = lean_ctor_get(v___x_1485_, 8);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1485_, 5);
lean_dec(v_unused_1548_);
v___x_1495_ = v___x_1485_;
v_isShared_1496_ = v_isSharedCheck_1547_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snapshotTasks_1493_);
lean_inc(v_infoState_1492_);
lean_inc(v_messages_1491_);
lean_inc(v_traceState_1490_);
lean_inc(v_auxDeclNGen_1489_);
lean_inc(v_ngen_1488_);
lean_inc(v_nextMacroScope_1487_);
lean_inc(v_env_1486_);
lean_dec(v___x_1485_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1547_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = l_Lean_Environment_setExporting(v_env_1486_, v_isExporting_1473_);
v___x_1498_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 5, v___x_1498_);
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_nextMacroScope_1487_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_ngen_1488_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_auxDeclNGen_1489_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_traceState_1490_);
lean_ctor_set(v_reuseFailAlloc_1546_, 5, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1546_, 6, v_messages_1491_);
lean_ctor_set(v_reuseFailAlloc_1546_, 7, v_infoState_1492_);
lean_ctor_set(v_reuseFailAlloc_1546_, 8, v_snapshotTasks_1493_);
v___x_1500_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_mctx_1503_; lean_object* v_zetaDeltaFVarIds_1504_; lean_object* v_postponed_1505_; lean_object* v_diag_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1544_; 
v___x_1501_ = lean_st_ref_set(v___y_1479_, v___x_1500_);
v___x_1502_ = lean_st_ref_take(v___y_1477_);
v_mctx_1503_ = lean_ctor_get(v___x_1502_, 0);
v_zetaDeltaFVarIds_1504_ = lean_ctor_get(v___x_1502_, 2);
v_postponed_1505_ = lean_ctor_get(v___x_1502_, 3);
v_diag_1506_ = lean_ctor_get(v___x_1502_, 4);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1502_, 1);
lean_dec(v_unused_1545_);
v___x_1508_ = v___x_1502_;
v_isShared_1509_ = v_isSharedCheck_1544_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_diag_1506_);
lean_inc(v_postponed_1505_);
lean_inc(v_zetaDeltaFVarIds_1504_);
lean_inc(v_mctx_1503_);
lean_dec(v___x_1502_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1544_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_mctx_1503_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_zetaDeltaFVarIds_1504_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_postponed_1505_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_diag_1506_);
v___x_1512_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v_r_1514_; 
v___x_1513_ = lean_st_ref_set(v___y_1477_, v___x_1512_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
v_r_1514_ = lean_apply_7(v_x_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
if (lean_obj_tag(v_r_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1531_; 
v_a_1515_ = lean_ctor_get(v_r_1514_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_r_1514_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1517_ = v_r_1514_;
v_isShared_1518_ = v_isSharedCheck_1531_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v_r_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1531_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
lean_inc(v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v___x_1521_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1479_, v_isExporting_1483_, v___x_1498_, v___y_1477_, v___x_1510_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1521_, 0);
lean_dec(v_unused_1529_);
v___x_1523_ = v___x_1521_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v___x_1521_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_a_1515_);
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1515_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1532_ = lean_ctor_get(v_r_1514_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v_r_1514_, 1);
v___x_1533_ = lean_box(0);
v___x_1534_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1479_, v_isExporting_1483_, v___x_1498_, v___y_1477_, v___x_1510_, v___x_1533_);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1534_, 0);
lean_dec(v_unused_1542_);
v___x_1536_ = v___x_1534_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v___x_1534_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 1);
lean_ctor_set(v___x_1536_, 0, v_a_1532_);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1532_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
}
}
v___jp_1549_:
{
if (v___y_1550_ == 0)
{
goto v___jp_1484_;
}
else
{
lean_object* v___x_1551_; 
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
v___x_1551_ = lean_apply_7(v_x_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1556_, lean_object* v_isExporting_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_isExporting_boxed_1565_; lean_object* v_res_1566_; 
v_isExporting_boxed_1565_ = lean_unbox(v_isExporting_1557_);
v_res_1566_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1556_, v_isExporting_boxed_1565_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1567_, uint8_t v_when_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
if (v_when_1568_ == 0)
{
lean_object* v___x_1576_; 
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
v___x_1576_ = lean_apply_7(v_x_1567_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, lean_box(0));
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = 0;
v___x_1578_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1567_, v___x_1577_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1579_, lean_object* v_when_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_when_boxed_1588_; lean_object* v_res_1589_; 
v_when_boxed_1588_ = lean_unbox(v_when_1580_);
v_res_1589_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1579_, v_when_boxed_1588_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1590_, size_t v_i_1591_, lean_object* v_bs_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_usize_dec_lt(v_i_1591_, v_sz_1590_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_bs_1592_);
return v___x_1597_;
}
else
{
lean_object* v_v_1598_; lean_object* v_ref_1599_; uint8_t v_kind_1600_; lean_object* v_levelParams_1601_; lean_object* v_modifiers_1602_; lean_object* v_declName_1603_; lean_object* v_binders_1604_; lean_object* v_numSectionVars_1605_; lean_object* v_type_1606_; lean_object* v_value_1607_; lean_object* v_termination_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1631_; 
v_v_1598_ = lean_array_uget(v_bs_1592_, v_i_1591_);
v_ref_1599_ = lean_ctor_get(v_v_1598_, 0);
v_kind_1600_ = lean_ctor_get_uint8(v_v_1598_, sizeof(void*)*9);
v_levelParams_1601_ = lean_ctor_get(v_v_1598_, 1);
v_modifiers_1602_ = lean_ctor_get(v_v_1598_, 2);
v_declName_1603_ = lean_ctor_get(v_v_1598_, 3);
v_binders_1604_ = lean_ctor_get(v_v_1598_, 4);
v_numSectionVars_1605_ = lean_ctor_get(v_v_1598_, 5);
v_type_1606_ = lean_ctor_get(v_v_1598_, 6);
v_value_1607_ = lean_ctor_get(v_v_1598_, 7);
v_termination_1608_ = lean_ctor_get(v_v_1598_, 8);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_v_1598_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1610_ = v_v_1598_;
v_isShared_1611_ = v_isSharedCheck_1631_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_termination_1608_);
lean_inc(v_value_1607_);
lean_inc(v_type_1606_);
lean_inc(v_numSectionVars_1605_);
lean_inc(v_binders_1604_);
lean_inc(v_declName_1603_);
lean_inc(v_modifiers_1602_);
lean_inc(v_levelParams_1601_);
lean_inc(v_ref_1599_);
lean_dec(v_v_1598_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1631_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Elab_WF_floatRecApp(v_value_1607_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; lean_object* v___x_1617_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1592_, v_i_1591_, v___x_1614_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 7, v_a_1613_);
v___x_1617_ = v___x_1610_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_ref_1599_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_levelParams_1601_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_modifiers_1602_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_declName_1603_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_binders_1604_);
lean_ctor_set(v_reuseFailAlloc_1622_, 5, v_numSectionVars_1605_);
lean_ctor_set(v_reuseFailAlloc_1622_, 6, v_type_1606_);
lean_ctor_set(v_reuseFailAlloc_1622_, 7, v_a_1613_);
lean_ctor_set(v_reuseFailAlloc_1622_, 8, v_termination_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1622_, sizeof(void*)*9, v_kind_1600_);
v___x_1617_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
size_t v___x_1618_; size_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = ((size_t)1ULL);
v___x_1619_ = lean_usize_add(v_i_1591_, v___x_1618_);
v___x_1620_ = lean_array_uset(v_bs_x27_1615_, v_i_1591_, v___x_1617_);
v_i_1591_ = v___x_1619_;
v_bs_1592_ = v___x_1620_;
goto _start;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_del_object(v___x_1610_);
lean_dec_ref(v_termination_1608_);
lean_dec_ref(v_type_1606_);
lean_dec(v_numSectionVars_1605_);
lean_dec(v_binders_1604_);
lean_dec(v_declName_1603_);
lean_dec_ref(v_modifiers_1602_);
lean_dec(v_levelParams_1601_);
lean_dec(v_ref_1599_);
lean_dec_ref(v_bs_1592_);
v_a_1623_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1612_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1612_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1632_, lean_object* v_i_1633_, lean_object* v_bs_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1632_);
lean_dec(v_sz_1632_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1633_);
lean_dec(v_i_1633_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1638_, v_i_boxed_1639_, v_bs_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t v_sz_1641_, size_t v_i_1642_, lean_object* v_bs_1643_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_usize_dec_lt(v_i_1642_, v_sz_1641_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_bs_1643_);
return v___x_1645_;
}
else
{
lean_object* v_v_1646_; 
v_v_1646_ = lean_array_uget_borrowed(v_bs_1643_, v_i_1642_);
if (lean_obj_tag(v_v_1646_) == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v_bs_1643_);
v___x_1647_ = lean_box(0);
return v___x_1647_;
}
else
{
lean_object* v_val_1648_; lean_object* v___x_1649_; lean_object* v_bs_x27_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v_val_1648_ = lean_ctor_get(v_v_1646_, 0);
lean_inc(v_val_1648_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v_bs_x27_1650_ = lean_array_uset(v_bs_1643_, v_i_1642_, v___x_1649_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1642_, v___x_1651_);
v___x_1653_ = lean_array_uset(v_bs_x27_1650_, v_i_1642_, v_val_1648_);
v_i_1642_ = v___x_1652_;
v_bs_1643_ = v___x_1653_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_sz_1655_, lean_object* v_i_1656_, lean_object* v_bs_1657_){
_start:
{
size_t v_sz_boxed_1658_; size_t v_i_boxed_1659_; lean_object* v_res_1660_; 
v_sz_boxed_1658_ = lean_unbox_usize(v_sz_1655_);
lean_dec(v_sz_1655_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_1658_, v_i_boxed_1659_, v_bs_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1661_, size_t v_i_1662_, lean_object* v_bs_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_usize_dec_lt(v_i_1662_, v_sz_1661_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_bs_1663_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; lean_object* v_v_1672_; lean_object* v___x_1673_; 
v___x_1671_ = 0;
v_v_1672_ = lean_array_uget_borrowed(v_bs_1663_, v_i_1662_);
lean_inc(v_v_1672_);
v___x_1673_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1672_, v___x_1671_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v_bs_x27_1676_; size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = lean_unsigned_to_nat(0u);
v_bs_x27_1676_ = lean_array_uset(v_bs_1663_, v_i_1662_, v___x_1675_);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1662_, v___x_1677_);
v___x_1679_ = lean_array_uset(v_bs_x27_1676_, v_i_1662_, v_a_1674_);
v_i_1662_ = v___x_1678_;
v_bs_1663_ = v___x_1679_;
goto _start;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_bs_1663_);
v_a_1681_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1673_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1673_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_bs_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1697_, v_i_boxed_1698_, v_bs_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v_env_1710_; lean_object* v_a_1712_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1709_ = lean_st_ref_get(v___y_1707_);
v_env_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_env_1710_);
lean_dec(v___x_1709_);
v___x_1722_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1700_, v___y_1705_, v___y_1707_);
lean_dec_ref(v___x_1722_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1723_ = lean_apply_7(v_x_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, lean_box(0));
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1710_, v___y_1705_, v___y_1707_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1725_, 0);
lean_dec(v_unused_1733_);
v___x_1727_ = v___x_1725_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v___x_1725_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_a_1724_);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1724_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1723_, 1);
v_a_1712_ = v_a_1734_;
goto v___jp_1711_;
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v___x_1713_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1710_, v___y_1705_, v___y_1707_);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v___x_1713_, 0);
lean_dec(v_unused_1721_);
v___x_1715_ = v___x_1713_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_dec(v___x_1713_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 1);
lean_ctor_set(v___x_1715_, 0, v_a_1712_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1735_, lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1735_, v_x_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1745_, lean_object* v_as_1746_, size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_a_1756_; uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v___x_1745_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1749_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; uint8_t v_kind_1763_; lean_object* v_declName_1764_; lean_object* v_type_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_a_1762_ = lean_array_uget_borrowed(v_as_1746_, v_i_1748_);
v_kind_1763_ = lean_ctor_get_uint8(v_a_1762_, sizeof(void*)*9);
v_declName_1764_ = lean_ctor_get(v_a_1762_, 3);
v_type_1765_ = lean_ctor_get(v_a_1762_, 6);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_name_eq(v_declName_1764_, v___x_1745_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1763_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_inc_ref(v_type_1765_);
v___x_1769_ = l_Lean_Meta_isProp(v_type_1765_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; uint8_t v___x_1771_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = lean_unbox(v_a_1770_);
lean_dec(v_a_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_inc(v___x_1745_);
lean_inc(v_a_1762_);
v___x_1772_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1762_, v___x_1745_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref_known(v___x_1772_, 1);
v_a_1756_ = v___x_1766_;
goto v___jp_1755_;
}
else
{
lean_dec(v___x_1745_);
return v___x_1772_;
}
}
else
{
v_a_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v___x_1745_);
v_a_1773_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1769_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
v_a_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
else
{
v_a_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
v___jp_1755_:
{
size_t v___x_1757_; size_t v___x_1758_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1748_, v___x_1757_);
v_i_1748_ = v___x_1758_;
v_b_1749_ = v_a_1756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1781_, lean_object* v_as_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1781_, v_as_1782_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_as_1782_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1808_ = l_Lean_stringToMessageData(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1814_, lean_object* v_preDefs_1815_, lean_object* v_termMeasure_x3fs_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
size_t v_sz_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v_sz_1824_ = lean_array_size(v_preDefs_1815_);
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1824_, v___x_1825_, v_preDefs_1815_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v_env_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; size_t v_sz_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_n(v_a_1827_, 2);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_st_ref_get(v_a_1822_);
v_env_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_ref(v_env_1829_);
lean_dec(v___x_1828_);
v___x_1830_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1831_ = lean_box(0);
v_sz_1845_ = lean_array_size(v_a_1827_);
v___x_1846_ = lean_box_usize(v_sz_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1848_, 0, v_a_1827_);
lean_closure_set(v___f_1848_, 1, v___x_1846_);
lean_closure_set(v___f_1848_, 2, v___x_1847_);
lean_closure_set(v___f_1848_, 3, v___x_1831_);
lean_closure_set(v___f_1848_, 4, v___x_1830_);
v___x_1849_ = l_Lean_Environment_unlockAsync(v_env_1829_);
v___x_1850_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1849_, v___f_1848_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_snd_1852_; lean_object* v_fst_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_2040_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v_snd_1852_ = lean_ctor_get(v_a_1851_, 1);
v_fst_1853_ = lean_ctor_get(v_a_1851_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_1851_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1855_ = v_a_1851_;
v_isShared_1856_ = v_isSharedCheck_2040_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_snd_1852_);
lean_inc(v_fst_1853_);
lean_dec(v_a_1851_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_2040_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_2039_; 
v_fst_1857_ = lean_ctor_get(v_snd_1852_, 0);
v_snd_1858_ = lean_ctor_get(v_snd_1852_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_snd_1852_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_1860_ = v_snd_1852_;
v_isShared_1861_ = v_isSharedCheck_2039_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v_snd_1852_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_2039_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v_wf_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___x_1967_; lean_object* v_a_1968_; lean_object* v___f_1969_; size_t v_sz_1970_; lean_object* v_termMeasures_x3f_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; uint8_t v___x_2032_; 
v___x_1921_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1967_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1921_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
lean_inc(v_snd_1858_);
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1969_, 0, v_snd_1858_);
v_sz_1970_ = lean_array_size(v_termMeasure_x3fs_1816_);
v_termMeasures_x3f_1971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_1970_, v___x_1825_, v_termMeasure_x3fs_1816_);
v___x_2032_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
if (v___x_2032_ == 0)
{
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
v___y_1997_ = v_a_1819_;
v___y_1998_ = v_a_1820_;
v___y_1999_ = v_a_1821_;
v___y_2000_ = v_a_1822_;
goto v___jp_1994_;
}
else
{
lean_object* v_value_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_value_2033_ = lean_ctor_get(v_snd_1858_, 7);
v___x_2034_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2033_);
v___x_2035_ = l_Lean_MessageData_ofExpr(v_value_2033_);
v___x_2036_ = l_Lean_indentD(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2034_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1921_, v___x_2037_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
v___y_1997_ = v_a_1819_;
v___y_1998_ = v_a_1820_;
v___y_1999_ = v_a_1821_;
v___y_2000_ = v_a_1822_;
goto v___jp_1994_;
}
else
{
lean_dec(v_termMeasures_x3f_1971_);
lean_dec_ref(v___f_1969_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
return v___x_2038_;
}
}
v___jp_1862_:
{
lean_object* v___x_1872_; 
lean_inc_ref(v___y_1864_);
lean_inc(v_a_1827_);
lean_inc(v_fst_1857_);
lean_inc(v_fst_1853_);
v___x_1872_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1853_, v_fst_1857_, v_a_1827_, v___y_1864_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
lean_inc_ref(v___y_1864_);
lean_inc(v_a_1827_);
lean_inc_ref(v_docCtx_1814_);
v___x_1874_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1814_, v_a_1827_, v_a_1873_, v___y_1864_, v___y_1863_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v_a_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1875_; 
lean_dec_ref_known(v___x_1874_, 1);
lean_inc(v_a_1827_);
v___x_1875_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1814_, v_a_1827_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref_known(v___x_1875_, 1);
v___x_1876_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1858_, v___y_1863_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1845_, v___x_1825_, v_a_1827_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v_declName_1880_; lean_object* v___x_1881_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc_n(v_a_1879_, 2);
lean_dec_ref_known(v___x_1878_, 1);
v_declName_1880_ = lean_ctor_get(v___y_1864_, 3);
lean_inc_n(v_declName_1880_, 2);
lean_dec_ref(v___y_1864_);
v___x_1881_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1879_, v_declName_1880_, v_fst_1853_, v_fst_1857_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_declName_1882_; lean_object* v_type_1883_; lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1881_, 1);
v_declName_1882_ = lean_ctor_get(v_a_1877_, 3);
v_type_1883_ = lean_ctor_get(v_a_1877_, 6);
lean_inc(v_declName_1882_);
v___x_1884_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1882_, v___y_1871_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref_known(v___x_1884_, 1);
lean_inc_ref(v_type_1883_);
v___x_1885_ = l_Lean_Meta_isProp(v_type_1883_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; uint8_t v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_inc(v_declName_1880_);
v___x_1888_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1877_, v_declName_1880_, v___y_1865_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_dec_ref_known(v___x_1888_, 1);
v___y_1833_ = v_declName_1880_;
v___y_1834_ = v_a_1879_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
v___y_1837_ = v___y_1868_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1870_;
v___y_1840_ = v___y_1871_;
goto v___jp_1832_;
}
else
{
lean_dec(v_declName_1880_);
lean_dec(v_a_1879_);
return v___x_1888_;
}
}
else
{
lean_dec(v_a_1877_);
lean_dec_ref(v___y_1865_);
v___y_1833_ = v_declName_1880_;
v___y_1834_ = v_a_1879_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
v___y_1837_ = v___y_1868_;
v___y_1838_ = v___y_1869_;
v___y_1839_ = v___y_1870_;
v___y_1840_ = v___y_1871_;
goto v___jp_1832_;
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_declName_1880_);
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_dec_ref(v___y_1865_);
v_a_1889_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1885_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_dec(v_declName_1880_);
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_dec_ref(v___y_1865_);
return v___x_1884_;
}
}
else
{
lean_dec(v_declName_1880_);
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_dec_ref(v___y_1865_);
return v___x_1881_;
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1877_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
v_a_1897_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1878_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1878_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
v_a_1905_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1876_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1876_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
return v___x_1875_;
}
}
else
{
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
return v___x_1874_;
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
v_a_1913_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1872_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1872_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
v___jp_1922_:
{
lean_object* v_declName_1932_; lean_object* v_type_1933_; lean_object* v_numFixed_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; 
v_declName_1932_ = lean_ctor_get(v_snd_1858_, 3);
v_type_1933_ = lean_ctor_get(v_snd_1858_, 6);
v_numFixed_1934_ = lean_ctor_get(v_fst_1853_, 0);
v___x_1935_ = lean_box_usize(v_sz_1845_);
v___x_1936_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1853_);
lean_inc(v_declName_1932_);
lean_inc(v_fst_1857_);
lean_inc(v_snd_1858_);
lean_inc(v_a_1827_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1937_, 0, v___x_1935_);
lean_closure_set(v___f_1937_, 1, v___x_1936_);
lean_closure_set(v___f_1937_, 2, v_a_1827_);
lean_closure_set(v___f_1937_, 3, v___y_1923_);
lean_closure_set(v___f_1937_, 4, v_snd_1858_);
lean_closure_set(v___f_1937_, 5, v_fst_1857_);
lean_closure_set(v___f_1937_, 6, v___x_1831_);
lean_closure_set(v___f_1937_, 7, v___x_1921_);
lean_closure_set(v___f_1937_, 8, v_declName_1932_);
lean_closure_set(v___f_1937_, 9, v_fst_1853_);
lean_closure_set(v___f_1937_, 10, v_wf_1925_);
lean_inc(v_numFixed_1934_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_numFixed_1934_);
v___x_1939_ = 0;
lean_inc_ref(v_type_1933_);
v___x_1940_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1933_, v___x_1938_, v___f_1937_, v___x_1939_, v___x_1939_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v_a_1943_; uint8_t v___x_1944_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1921_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref(v___x_1942_);
v___x_1944_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1944_ == 0)
{
lean_del_object(v___x_1860_);
lean_del_object(v___x_1855_);
v___y_1863_ = v___x_1939_;
v___y_1864_ = v_a_1941_;
v___y_1865_ = v___y_1924_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
v___y_1868_ = v___y_1928_;
v___y_1869_ = v___y_1929_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1931_;
goto v___jp_1862_;
}
else
{
lean_object* v_declName_1945_; lean_object* v_value_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_declName_1945_ = lean_ctor_get(v_a_1941_, 3);
v_value_1946_ = lean_ctor_get(v_a_1941_, 7);
v___x_1947_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1945_);
v___x_1948_ = l_Lean_MessageData_ofName(v_declName_1945_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 7);
lean_ctor_set(v___x_1860_, 1, v___x_1948_);
lean_ctor_set(v___x_1860_, 0, v___x_1947_);
v___x_1950_ = v___x_1860_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 7);
lean_ctor_set(v___x_1855_, 1, v___x_1951_);
lean_ctor_set(v___x_1855_, 0, v___x_1950_);
v___x_1953_ = v___x_1855_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_inc_ref(v_value_1946_);
v___x_1954_ = l_Lean_MessageData_ofExpr(v_value_1946_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1921_, v___x_1955_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec_ref_known(v___x_1956_, 1);
v___y_1863_ = v___x_1939_;
v___y_1864_ = v_a_1941_;
v___y_1865_ = v___y_1924_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
v___y_1868_ = v___y_1928_;
v___y_1869_ = v___y_1929_;
v___y_1870_ = v___y_1930_;
v___y_1871_ = v___y_1931_;
goto v___jp_1862_;
}
else
{
lean_dec(v_a_1941_);
lean_dec_ref(v___y_1924_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v___y_1924_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
v_a_1959_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1940_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1940_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
v___jp_1972_:
{
if (lean_obj_tag(v_termMeasures_x3f_1971_) == 1)
{
lean_object* v_val_1982_; 
lean_dec_ref(v___y_1974_);
v_val_1982_ = lean_ctor_get(v_termMeasures_x3f_1971_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v_termMeasures_x3f_1971_, 1);
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1975_;
v_wf_1925_ = v_val_1982_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
v___y_1928_ = v___y_1978_;
v___y_1929_ = v___y_1979_;
v___y_1930_ = v___y_1980_;
v___y_1931_ = v___y_1981_;
goto v___jp_1922_;
}
else
{
uint8_t v___x_1983_; lean_object* v___x_1984_; 
lean_dec(v_termMeasures_x3f_1971_);
v___x_1983_ = 1;
v___x_1984_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1974_, v___x_1983_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1975_;
v_wf_1925_ = v_a_1985_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
v___y_1928_ = v___y_1978_;
v___y_1929_ = v___y_1979_;
v___y_1930_ = v___y_1980_;
v___y_1931_ = v___y_1981_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v___y_1975_);
lean_dec_ref(v___y_1973_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
v_a_1986_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1984_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
v___jp_1994_:
{
lean_object* v___x_2001_; lean_object* v_env_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2001_ = lean_st_ref_get(v___y_2000_);
v_env_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref(v_env_2002_);
lean_dec(v___x_2001_);
v___x_2003_ = l_Lean_Environment_unlockAsync(v_env_2002_);
v___x_2004_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_2003_, v___f_1969_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2023_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_fst_2006_ = lean_ctor_get(v_a_2005_, 0);
v_snd_2007_ = lean_ctor_get(v_a_2005_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2009_ = v_a_2005_;
v_isShared_2010_ = v_isSharedCheck_2023_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2006_);
lean_dec(v_a_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2023_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___f_2013_; uint8_t v___x_2014_; 
v___x_2011_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1921_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
lean_inc(v_fst_1857_);
lean_inc(v_fst_1853_);
lean_inc(v_fst_2006_);
lean_inc(v_a_1827_);
v___f_2013_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2013_, 0, v_a_1827_);
lean_closure_set(v___f_2013_, 1, v_fst_2006_);
lean_closure_set(v___f_2013_, 2, v_fst_1853_);
lean_closure_set(v___f_2013_, 3, v_fst_1857_);
v___x_2014_ = lean_unbox(v_a_2012_);
lean_dec(v_a_2012_);
if (v___x_2014_ == 0)
{
lean_del_object(v___x_2009_);
v___y_1973_ = v_fst_2006_;
v___y_1974_ = v___f_2013_;
v___y_1975_ = v_snd_2007_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
goto v___jp_1972_;
}
else
{
lean_object* v_value_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v_value_2015_ = lean_ctor_get(v_snd_1858_, 7);
v___x_2016_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2015_);
v___x_2017_ = l_Lean_MessageData_ofExpr(v_value_2015_);
v___x_2018_ = l_Lean_indentD(v___x_2017_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2018_);
lean_ctor_set(v___x_2009_, 0, v___x_2016_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1921_, v___x_2020_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_dec_ref_known(v___x_2021_, 1);
v___y_1973_ = v_fst_2006_;
v___y_1974_ = v___f_2013_;
v___y_1975_ = v_snd_2007_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___y_1997_;
v___y_1979_ = v___y_1998_;
v___y_1980_ = v___y_1999_;
v___y_1981_ = v___y_2000_;
goto v___jp_1972_;
}
else
{
lean_dec_ref(v___f_2013_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_termMeasures_x3f_1971_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_termMeasures_x3f_1971_);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_del_object(v___x_1855_);
lean_dec(v_fst_1853_);
lean_dec(v_a_1827_);
lean_dec_ref(v_docCtx_1814_);
v_a_2024_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2004_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2004_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_1827_);
lean_dec_ref(v_termMeasure_x3fs_1816_);
lean_dec_ref(v_docCtx_1814_);
v_a_2041_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1850_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1850_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
v___jp_1832_:
{
size_t v_sz_1841_; lean_object* v___x_1842_; 
v_sz_1841_ = lean_array_size(v___y_1834_);
lean_inc(v___y_1833_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1833_, v___y_1834_, v_sz_1841_, v___x_1825_, v___x_1831_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; 
lean_dec_ref_known(v___x_1842_, 1);
v___x_1843_ = l_Lean_enableRealizationsForConst(v___y_1833_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref_known(v___x_1843_, 1);
v___x_1844_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1844_;
}
else
{
lean_dec_ref(v___y_1834_);
return v___x_1843_;
}
}
else
{
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_termMeasure_x3fs_1816_);
lean_dec_ref(v_docCtx_1814_);
v_a_2049_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_1826_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_1826_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2057_, lean_object* v_preDefs_2058_, lean_object* v_termMeasure_x3fs_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Elab_wfRecursion(v_docCtx_2057_, v_preDefs_2058_, v_termMeasure_x3fs_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2068_, lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2078_, v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2088_, size_t v_i_2089_, lean_object* v_bs_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2088_, v_i_2089_, v_bs_2090_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2099_, lean_object* v_i_2100_, lean_object* v_bs_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
size_t v_sz_boxed_2109_; size_t v_i_boxed_2110_; lean_object* v_res_2111_; 
v_sz_boxed_2109_ = lean_unbox_usize(v_sz_2099_);
lean_dec(v_sz_2099_);
v_i_boxed_2110_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2109_, v_i_boxed_2110_, v_bs_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2112_, size_t v_sz_2113_, size_t v_i_2114_, lean_object* v_b_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2112_, v_sz_2113_, v_i_2114_, v_b_2115_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2124_, lean_object* v_sz_2125_, lean_object* v_i_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
size_t v_sz_boxed_2135_; size_t v_i_boxed_2136_; lean_object* v_res_2137_; 
v_sz_boxed_2135_ = lean_unbox_usize(v_sz_2125_);
lean_dec(v_sz_2125_);
v_i_boxed_2136_ = lean_unbox_usize(v_i_2126_);
lean_dec(v_i_2126_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2124_, v_sz_boxed_2135_, v_i_boxed_2136_, v_b_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec_ref(v_as_2124_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2138_, lean_object* v_as_2139_, size_t v_sz_2140_, size_t v_i_2141_, lean_object* v_bs_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2138_, v_sz_2140_, v_i_2141_, v_bs_2142_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2151_, lean_object* v_as_2152_, lean_object* v_sz_2153_, lean_object* v_i_2154_, lean_object* v_bs_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
size_t v_sz_boxed_2163_; size_t v_i_boxed_2164_; lean_object* v_res_2165_; 
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2164_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2151_, v_as_2152_, v_sz_boxed_2163_, v_i_boxed_2164_, v_bs_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_as_2152_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2166_, lean_object* v___x_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_bs_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2166_, v___x_2167_, v_sz_2168_, v_i_2169_, v_bs_2170_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2179_, lean_object* v___x_2180_, lean_object* v_sz_2181_, lean_object* v_i_2182_, lean_object* v_bs_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2181_);
lean_dec(v_sz_2181_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2179_, v___x_2180_, v_sz_boxed_2191_, v_i_boxed_2192_, v_bs_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2194_, lean_object* v_env_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2195_, v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_env_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2205_, v_env_2206_, v_x_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2216_, lean_object* v_msg_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2216_, v_msg_2217_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2226_, lean_object* v_msg_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2226_, v_msg_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_bs_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2236_, v_i_2237_, v_bs_2238_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_bs_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
size_t v_sz_boxed_2257_; size_t v_i_boxed_2258_; lean_object* v_res_2259_; 
v_sz_boxed_2257_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2258_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2257_, v_i_boxed_2258_, v_bs_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2260_, lean_object* v_as_2261_, size_t v_sz_2262_, size_t v_i_2263_, lean_object* v_b_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2260_, v_as_2261_, v_sz_2262_, v_i_2263_, v_b_2264_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2273_, lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; lean_object* v_res_2287_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2273_, v_as_2274_, v_sz_boxed_2285_, v_i_boxed_2286_, v_b_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2274_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2288_, lean_object* v_x_2289_, uint8_t v_isExporting_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2289_, v_isExporting_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_x_2300_, lean_object* v_isExporting_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v_isExporting_boxed_2309_; lean_object* v_res_2310_; 
v_isExporting_boxed_2309_ = lean_unbox(v_isExporting_2301_);
v_res_2310_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2299_, v_x_2300_, v_isExporting_boxed_2309_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2311_, lean_object* v_x_2312_, uint8_t v_when_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2312_, v_when_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_x_2323_, lean_object* v_when_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_when_boxed_2332_; lean_object* v_res_2333_; 
v_when_boxed_2332_ = lean_unbox(v_when_2324_);
v_res_2333_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2322_, v_x_2323_, v_when_boxed_2332_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2334_, lean_object* v_macroStack_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2334_, v_macroStack_2335_, v___y_2340_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2344_, lean_object* v_macroStack_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2344_, v_macroStack_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2354_, lean_object* v_msgData_2355_, uint8_t v_severity_2356_, uint8_t v_isSilent_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2354_, v_msgData_2355_, v_severity_2356_, v_isSilent_2357_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2366_, lean_object* v_msgData_2367_, lean_object* v_severity_2368_, lean_object* v_isSilent_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
uint8_t v_severity_boxed_2377_; uint8_t v_isSilent_boxed_2378_; lean_object* v_res_2379_; 
v_severity_boxed_2377_ = lean_unbox(v_severity_2368_);
v_isSilent_boxed_2378_ = lean_unbox(v_isSilent_2369_);
v_res_2379_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2366_, v_msgData_2367_, v_severity_boxed_2377_, v_isSilent_boxed_2378_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v_ref_2366_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2450_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2451_ = 0;
v___x_2452_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2453_ = l_Lean_registerTraceClass(v___x_2450_, v___x_2451_, v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2455_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
