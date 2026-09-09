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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v___x_26_ = lean_st_ref_put(v___y_10_, v___x_25_);
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
v___x_38_ = lean_st_ref_put(v___y_9_, v___x_37_);
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
lean_object* v_toCold_216_; lean_object* v_options_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_toCold_216_ = lean_ctor_get(v___y_214_, 0);
v_options_217_ = lean_ctor_get(v_toCold_216_, 2);
v___x_218_ = l_Lean_Elab_pp_macroStack;
v___x_219_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec(v_macroStack_213_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_msgData_212_);
return v___x_220_;
}
else
{
if (lean_obj_tag(v_macroStack_213_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_msgData_212_);
return v___x_221_;
}
else
{
lean_object* v_head_222_; lean_object* v_after_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_238_; 
v_head_222_ = lean_ctor_get(v_macroStack_213_, 0);
lean_inc(v_head_222_);
v_after_223_ = lean_ctor_get(v_head_222_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_head_222_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_head_222_, 0);
lean_dec(v_unused_239_);
v___x_225_ = v_head_222_;
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_after_223_);
lean_dec(v_head_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_238_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 7);
lean_ctor_set(v___x_225_, 1, v___x_227_);
lean_ctor_set(v___x_225_, 0, v_msgData_212_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_msgData_212_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_237_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_msgData_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_MessageData_ofSyntax(v_after_223_);
v___x_233_ = l_Lean_indentD(v___x_232_);
v_msgData_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_234_, 0, v___x_231_);
lean_ctor_set(v_msgData_234_, 1, v___x_233_);
v___x_235_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_234_, v_macroStack_213_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
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
lean_object* v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v_toCold_254_; lean_object* v_mctx_255_; lean_object* v_lctx_256_; lean_object* v_options_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_251_ = lean_st_ref_get(v___y_249_);
v_env_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_env_252_);
lean_dec(v___x_251_);
v___x_253_ = lean_st_ref_get(v___y_247_);
v_toCold_254_ = lean_ctor_get(v___y_248_, 0);
v_mctx_255_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_255_);
lean_dec(v___x_253_);
v_lctx_256_ = lean_ctor_get(v___y_246_, 2);
v_options_257_ = lean_ctor_get(v_toCold_254_, 2);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_lctx_256_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_env_252_);
lean_ctor_set(v___x_258_, 1, v_mctx_255_);
lean_ctor_set(v___x_258_, 2, v_lctx_256_);
lean_ctor_set(v___x_258_, 3, v_options_257_);
v___x_259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_msgData_245_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_ref_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v_macroStack_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_ref_276_ = lean_ctor_get(v___y_273_, 2);
v___x_277_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_268_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref(v___x_277_);
v_macroStack_279_ = lean_ctor_get(v___y_269_, 1);
v___x_280_ = l_Lean_Elab_getBetterRef(v_ref_276_, v_macroStack_279_);
lean_inc(v_macroStack_279_);
v___x_281_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_278_, v_macroStack_279_, v___y_273_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_280_);
lean_ctor_set(v___x_286_, 1, v_a_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set_tag(v___x_284_, 1);
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_as_306_, size_t v_sz_307_, size_t v_i_308_, lean_object* v_b_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_a_318_; uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v_b_309_);
return v___x_323_;
}
else
{
lean_object* v_array_324_; lean_object* v_start_325_; lean_object* v_stop_326_; uint8_t v___x_327_; 
v_array_324_ = lean_ctor_get(v_b_309_, 0);
v_start_325_ = lean_ctor_get(v_b_309_, 1);
v_stop_326_ = lean_ctor_get(v_b_309_, 2);
v___x_327_ = lean_nat_dec_lt(v_start_325_, v_stop_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v_b_309_);
return v___x_328_;
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_357_; 
lean_inc(v_stop_326_);
lean_inc(v_start_325_);
lean_inc_ref(v_array_324_);
v_isSharedCheck_357_ = !lean_is_exclusive(v_b_309_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_358_ = lean_ctor_get(v_b_309_, 2);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_b_309_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_b_309_, 0);
lean_dec(v_unused_360_);
v___x_330_ = v_b_309_;
v_isShared_331_ = v_isSharedCheck_357_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_b_309_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_357_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v_a_332_ = lean_array_uget_borrowed(v_as_306_, v_i_308_);
v___x_333_ = lean_array_fget(v_array_324_, v_start_325_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_start_325_, v___x_334_);
lean_dec(v_start_325_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_335_);
v___x_337_ = v___x_330_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_array_324_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_stop_326_);
v___x_337_ = v_reuseFailAlloc_356_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_array_get_size(v_a_332_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v___x_333_);
v_a_318_ = v___x_337_;
goto v___jp_317_;
}
else
{
lean_object* v_declName_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_declName_341_ = lean_ctor_get(v___x_333_, 3);
lean_inc(v_declName_341_);
lean_dec(v___x_333_);
v___x_342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
v___x_343_ = l_Lean_MessageData_ofName(v_declName_341_);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_346_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_dec_ref_known(v___x_347_, 1);
v_a_318_ = v___x_337_;
goto v___jp_317_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v___x_337_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
}
}
v___jp_317_:
{
size_t v___x_319_; size_t v___x_320_; 
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_add(v_i_308_, v___x_319_);
v_i_308_ = v___x_320_;
v_b_309_ = v_a_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_as_361_, lean_object* v_sz_362_, lean_object* v_i_363_, lean_object* v_b_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
size_t v_sz_boxed_372_; size_t v_i_boxed_373_; lean_object* v_res_374_; 
v_sz_boxed_372_ = lean_unbox_usize(v_sz_362_);
lean_dec(v_sz_362_);
v_i_boxed_373_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_361_, v_sz_boxed_372_, v_i_boxed_373_, v_b_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec_ref(v_as_361_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_375_, size_t v_sz_376_, size_t v_i_377_, lean_object* v_bs_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_usize_dec_lt(v_i_377_, v_sz_376_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v_a_375_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_bs_378_);
return v___x_385_;
}
else
{
lean_object* v_v_386_; lean_object* v___x_387_; lean_object* v_bs_x27_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_v_386_ = lean_array_uget(v_bs_378_, v_i_377_);
v___x_387_ = lean_unsigned_to_nat(0u);
v_bs_x27_388_ = lean_array_uset(v_bs_378_, v_i_377_, v___x_387_);
v___x_389_ = lean_usize_to_nat(v_i_377_);
lean_inc_ref(v_a_375_);
v___x_390_ = l_Lean_Elab_WF_varyingVarNames(v_a_375_, v___x_389_, v_v_386_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_377_, v___x_392_);
v___x_394_ = lean_array_uset(v_bs_x27_388_, v_i_377_, v_a_391_);
v_i_377_ = v___x_393_;
v_bs_378_ = v___x_394_;
goto _start;
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_bs_x27_388_);
lean_dec_ref(v_a_375_);
v_a_396_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_390_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_390_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_414_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_404_, v_sz_boxed_413_, v_i_boxed_414_, v_bs_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object* v_as_416_, size_t v_sz_417_, size_t v_i_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_lt(v_i_418_, v_sz_417_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v_b_419_);
return v___x_424_;
}
else
{
lean_object* v_a_425_; lean_object* v___x_426_; 
v_a_425_ = lean_array_uget_borrowed(v_as_416_, v_i_418_);
v___x_426_ = l_Lean_Elab_addAsAxiom___redArg(v_a_425_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; 
lean_dec_ref_known(v___x_426_, 1);
v___x_427_ = lean_box(0);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_418_, v___x_428_);
v_i_418_ = v___x_429_;
v_b_419_ = v___x_427_;
goto _start;
}
else
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_as_431_, lean_object* v_sz_432_, lean_object* v_i_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
size_t v_sz_boxed_438_; size_t v_i_boxed_439_; lean_object* v_res_440_; 
v_sz_boxed_438_ = lean_unbox_usize(v_sz_432_);
lean_dec(v_sz_432_);
v_i_boxed_439_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_431_, v_sz_boxed_438_, v_i_boxed_439_, v_b_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec_ref(v_as_431_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t v_sz_441_, size_t v_i_442_, lean_object* v_bs_443_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_456_, v_i_boxed_457_, v_bs_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object* v_a_459_, lean_object* v___x_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_bs_463_, lean_object* v___y_464_, lean_object* v___y_465_){
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
size_t v_sz_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_sz_483_ = lean_array_size(v_a_459_);
v___x_484_ = ((size_t)0ULL);
lean_inc_ref(v_a_459_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_483_, v___x_484_, v_a_459_);
lean_inc(v___x_460_);
v___x_486_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_485_, v___x_460_, v_value_478_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v_bs_x27_489_; lean_object* v___x_491_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = lean_unsigned_to_nat(0u);
v_bs_x27_489_ = lean_array_uset(v_bs_463_, v_i_462_, v___x_488_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 7, v_a_487_);
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
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_a_487_);
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
v___x_494_ = lean_array_uset(v_bs_x27_489_, v_i_462_, v___x_491_);
v_i_462_ = v___x_493_;
v_bs_463_ = v___x_494_;
goto _start;
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_481_);
lean_dec_ref(v_termination_479_);
lean_dec_ref(v_type_477_);
lean_dec(v_numSectionVars_476_);
lean_dec(v_binders_475_);
lean_dec(v_declName_474_);
lean_dec_ref(v_modifiers_473_);
lean_dec(v_levelParams_472_);
lean_dec(v_ref_470_);
lean_dec_ref(v_bs_463_);
lean_dec(v___x_460_);
lean_dec_ref(v_a_459_);
v_a_497_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_486_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_486_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* v_a_506_, lean_object* v___x_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_515_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_506_, v___x_507_, v_sz_boxed_514_, v_i_boxed_515_, v_bs_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_517_, size_t v_sz_518_, size_t v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_517_, v_sz_518_, v___x_519_, v___x_520_, v___y_526_, v___y_527_);
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
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_531_, v_sz_518_, v___x_519_, v_a_517_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
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
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_533_, v_sz_537_, v___x_519_, v___x_536_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v_numSectionVars_540_; lean_object* v___x_541_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_539_ = lean_array_get_borrowed(v___x_521_, v_a_517_, v___x_534_);
v_numSectionVars_540_ = lean_ctor_get(v___x_539_, 5);
lean_inc(v_numSectionVars_540_);
lean_inc_ref(v_a_517_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_517_, v_numSectionVars_540_, v_sz_518_, v___x_519_, v_a_517_, v___y_526_, v___y_527_);
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
size_t v_sz_boxed_614_; size_t v___x_43771__boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v___x_43771__boxed_615_ = lean_unbox_usize(v___x_604_);
lean_dec(v___x_604_);
v_res_616_ = l_Lean_Elab_wfRecursion___lam__0(v_a_602_, v_sz_boxed_614_, v___x_43771__boxed_615_, v___x_605_, v___x_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v___x_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_toCold_628_; lean_object* v_options_629_; uint8_t v_hasTrace_630_; 
v_toCold_628_ = lean_ctor_get(v___y_625_, 0);
v_options_629_ = lean_ctor_get(v_toCold_628_, 2);
v_hasTrace_630_ = lean_ctor_get_uint8(v_options_629_, sizeof(void*)*1);
if (v_hasTrace_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v___x_620_);
v___x_631_ = lean_box(v_hasTrace_630_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
else
{
lean_object* v_inheritedTraceOptions_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_inheritedTraceOptions_633_ = lean_ctor_get(v_toCold_628_, 11);
v___x_634_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
v___x_635_ = l_Lean_Name_append(v___x_634_, v___x_620_);
v___x_636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_633_, v_options_629_, v___x_635_);
lean_dec(v___x_635_);
v___x_637_ = lean_box(v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v___x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_wfRecursion___lam__1(v___x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v_snd_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_648_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_ref_657_; uint8_t v_kind_658_; lean_object* v_levelParams_659_; lean_object* v_modifiers_660_; lean_object* v_declName_661_; lean_object* v_binders_662_; lean_object* v_numSectionVars_663_; lean_object* v_type_664_; lean_object* v_value_665_; lean_object* v_termination_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref_known(v___x_656_, 1);
v_ref_657_ = lean_ctor_get(v_snd_648_, 0);
v_kind_658_ = lean_ctor_get_uint8(v_snd_648_, sizeof(void*)*9);
v_levelParams_659_ = lean_ctor_get(v_snd_648_, 1);
v_modifiers_660_ = lean_ctor_get(v_snd_648_, 2);
v_declName_661_ = lean_ctor_get(v_snd_648_, 3);
v_binders_662_ = lean_ctor_get(v_snd_648_, 4);
v_numSectionVars_663_ = lean_ctor_get(v_snd_648_, 5);
v_type_664_ = lean_ctor_get(v_snd_648_, 6);
v_value_665_ = lean_ctor_get(v_snd_648_, 7);
v_termination_666_ = lean_ctor_get(v_snd_648_, 8);
v_isSharedCheck_692_ = !lean_is_exclusive(v_snd_648_);
if (v_isSharedCheck_692_ == 0)
{
v___x_668_ = v_snd_648_;
v_isShared_669_ = v_isSharedCheck_692_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_termination_666_);
lean_inc(v_value_665_);
lean_inc(v_type_664_);
lean_inc(v_numSectionVars_663_);
lean_inc(v_binders_662_);
lean_inc(v_declName_661_);
lean_inc(v_modifiers_660_);
lean_inc(v_levelParams_659_);
lean_inc(v_ref_657_);
lean_dec(v_snd_648_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_692_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_WF_preprocess(v_value_665_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_683_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_683_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_683_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_expr_675_; lean_object* v___x_677_; 
v_expr_675_ = lean_ctor_get(v_a_671_, 0);
lean_inc_ref(v_expr_675_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 7, v_expr_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_ref_657_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_levelParams_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_modifiers_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_declName_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_binders_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_numSectionVars_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_type_664_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_expr_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_termination_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*9, v_kind_658_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_678_);
v___x_680_ = v___x_673_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_del_object(v___x_668_);
lean_dec_ref(v_termination_666_);
lean_dec_ref(v_type_664_);
lean_dec(v_numSectionVars_663_);
lean_dec(v_binders_662_);
lean_dec(v_declName_661_);
lean_dec_ref(v_modifiers_660_);
lean_dec(v_levelParams_659_);
lean_dec(v_ref_657_);
v_a_684_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_670_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_670_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_snd_648_);
v_a_693_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_656_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_656_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v_snd_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_wfRecursion___lam__2(v_snd_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
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
v___x_743_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__0));
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
uint8_t v_suppressElabErrors_boxed_748_; uint8_t v___y_44101__boxed_749_; uint8_t v_res_750_; lean_object* v_r_751_; 
v_suppressElabErrors_boxed_748_ = lean_unbox(v_suppressElabErrors_745_);
v___y_44101__boxed_749_ = lean_unbox(v___y_746_);
v_res_750_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_748_, v___y_44101__boxed_749_, v_x_747_);
lean_dec(v_x_747_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_753_, lean_object* v_msgData_754_, uint8_t v_severity_755_, uint8_t v_isSilent_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___y_763_; uint8_t v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; lean_object* v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; lean_object* v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; uint8_t v___y_842_; uint8_t v___x_847_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; uint8_t v___y_852_; lean_object* v___y_853_; uint8_t v___y_854_; uint8_t v___y_855_; uint8_t v___y_857_; uint8_t v___x_873_; 
v___x_847_ = 2;
v___x_873_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_847_);
if (v___x_873_ == 0)
{
v___y_857_ = v___x_873_;
goto v___jp_856_;
}
else
{
uint8_t v___x_874_; 
lean_inc_ref(v_msgData_754_);
v___x_874_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_754_);
v___y_857_ = v___x_874_;
goto v___jp_856_;
}
v___jp_762_:
{
lean_object* v___x_772_; lean_object* v_toCold_773_; lean_object* v_currNamespace_774_; lean_object* v_openDecls_775_; lean_object* v_env_776_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_traceState_780_; lean_object* v_cache_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_798_; 
v___x_772_ = lean_st_ref_take(v___y_771_);
v_toCold_773_ = lean_ctor_get(v___y_770_, 0);
v_currNamespace_774_ = lean_ctor_get(v_toCold_773_, 4);
v_openDecls_775_ = lean_ctor_get(v_toCold_773_, 5);
v_env_776_ = lean_ctor_get(v___x_772_, 0);
v_nextMacroScope_777_ = lean_ctor_get(v___x_772_, 1);
v_ngen_778_ = lean_ctor_get(v___x_772_, 2);
v_auxDeclNGen_779_ = lean_ctor_get(v___x_772_, 3);
v_traceState_780_ = lean_ctor_get(v___x_772_, 4);
v_cache_781_ = lean_ctor_get(v___x_772_, 5);
v_messages_782_ = lean_ctor_get(v___x_772_, 6);
v_infoState_783_ = lean_ctor_get(v___x_772_, 7);
v_snapshotTasks_784_ = lean_ctor_get(v___x_772_, 8);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_798_ == 0)
{
v___x_786_ = v___x_772_;
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snapshotTasks_784_);
lean_inc(v_infoState_783_);
lean_inc(v_messages_782_);
lean_inc(v_cache_781_);
lean_inc(v_traceState_780_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_ngen_778_);
lean_inc(v_nextMacroScope_777_);
lean_inc(v_env_776_);
lean_dec(v___x_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc(v_openDecls_775_);
lean_inc(v_currNamespace_774_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_currNamespace_774_);
lean_ctor_set(v___x_788_, 1, v_openDecls_775_);
v___x_789_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___y_766_);
lean_inc_ref(v___y_767_);
lean_inc_ref(v___y_769_);
v___x_790_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_790_, 0, v___y_769_);
lean_ctor_set(v___x_790_, 1, v___y_765_);
lean_ctor_set(v___x_790_, 2, v___y_763_);
lean_ctor_set(v___x_790_, 3, v___y_767_);
lean_ctor_set(v___x_790_, 4, v___x_789_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*5, v___y_764_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*5 + 1, v___y_768_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*5 + 2, v_isSilent_756_);
v___x_791_ = l_Lean_MessageLog_add(v___x_790_, v_messages_782_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 6, v___x_791_);
v___x_793_ = v___x_786_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_env_776_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_nextMacroScope_777_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_ngen_778_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_traceState_780_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_cache_781_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v_infoState_783_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_snapshotTasks_784_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_st_ref_put(v___y_771_, v___x_793_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
}
v___jp_799_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_823_; 
v___x_808_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_754_);
v___x_809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_808_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_823_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc_ref_n(v___y_802_, 2);
v___x_814_ = l_Lean_FileMap_toPosition(v___y_802_, v___y_803_);
lean_dec(v___y_803_);
v___x_815_ = l_Lean_FileMap_toPosition(v___y_802_, v___y_807_);
lean_dec(v___y_807_);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_806_ == 0)
{
lean_del_object(v___x_812_);
lean_dec_ref(v___y_800_);
v___y_763_ = v___x_816_;
v___y_764_ = v___y_801_;
v___y_765_ = v___x_814_;
v___y_766_ = v_a_810_;
v___y_767_ = v___x_817_;
v___y_768_ = v___y_804_;
v___y_769_ = v___y_805_;
v___y_770_ = v___y_759_;
v___y_771_ = v___y_760_;
goto v___jp_762_;
}
else
{
uint8_t v___x_818_; 
lean_inc(v_a_810_);
v___x_818_ = l_Lean_MessageData_hasTag(v___y_800_, v_a_810_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_816_, 1);
lean_dec_ref(v___x_814_);
lean_dec(v_a_810_);
v___x_819_ = lean_box(0);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_del_object(v___x_812_);
v___y_763_ = v___x_816_;
v___y_764_ = v___y_801_;
v___y_765_ = v___x_814_;
v___y_766_ = v_a_810_;
v___y_767_ = v___x_817_;
v___y_768_ = v___y_804_;
v___y_769_ = v___y_805_;
v___y_770_ = v___y_759_;
v___y_771_ = v___y_760_;
goto v___jp_762_;
}
}
}
}
v___jp_824_:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Syntax_getTailPos_x3f(v___y_826_, v___y_827_);
lean_dec(v___y_826_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_inc(v___y_832_);
v___y_800_ = v___y_825_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v___y_832_;
v___y_804_ = v___y_829_;
v___y_805_ = v___y_830_;
v___y_806_ = v___y_831_;
v___y_807_ = v___y_832_;
goto v___jp_799_;
}
else
{
lean_object* v_val_834_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___x_833_, 1);
v___y_800_ = v___y_825_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_828_;
v___y_803_ = v___y_832_;
v___y_804_ = v___y_829_;
v___y_805_ = v___y_830_;
v___y_806_ = v___y_831_;
v___y_807_ = v_val_834_;
goto v___jp_799_;
}
}
v___jp_835_:
{
lean_object* v_ref_843_; lean_object* v___x_844_; 
v_ref_843_ = l_Lean_replaceRef(v_ref_753_, v___y_838_);
v___x_844_ = l_Lean_Syntax_getPos_x3f(v_ref_843_, v___y_837_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___y_825_ = v___y_836_;
v___y_826_ = v_ref_843_;
v___y_827_ = v___y_837_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_842_;
v___y_830_ = v___y_840_;
v___y_831_ = v___y_841_;
v___y_832_ = v___x_845_;
goto v___jp_824_;
}
else
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_844_, 1);
v___y_825_ = v___y_836_;
v___y_826_ = v_ref_843_;
v___y_827_ = v___y_837_;
v___y_828_ = v___y_839_;
v___y_829_ = v___y_842_;
v___y_830_ = v___y_840_;
v___y_831_ = v___y_841_;
v___y_832_ = v_val_846_;
goto v___jp_824_;
}
}
v___jp_848_:
{
if (v___y_855_ == 0)
{
v___y_836_ = v___y_850_;
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___y_849_;
v___y_840_ = v___y_851_;
v___y_841_ = v___y_854_;
v___y_842_ = v_severity_755_;
goto v___jp_835_;
}
else
{
v___y_836_ = v___y_850_;
v___y_837_ = v___y_852_;
v___y_838_ = v___y_853_;
v___y_839_ = v___y_849_;
v___y_840_ = v___y_851_;
v___y_841_ = v___y_854_;
v___y_842_ = v___x_847_;
goto v___jp_835_;
}
}
v___jp_856_:
{
if (v___y_857_ == 0)
{
lean_object* v_toCold_858_; lean_object* v_ref_859_; uint8_t v_suppressElabErrors_860_; lean_object* v_fileName_861_; lean_object* v_fileMap_862_; lean_object* v_options_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___f_866_; uint8_t v___x_867_; uint8_t v___x_868_; 
v_toCold_858_ = lean_ctor_get(v___y_759_, 0);
v_ref_859_ = lean_ctor_get(v___y_759_, 2);
v_suppressElabErrors_860_ = lean_ctor_get_uint8(v___y_759_, sizeof(void*)*3 + 1);
v_fileName_861_ = lean_ctor_get(v_toCold_858_, 0);
v_fileMap_862_ = lean_ctor_get(v_toCold_858_, 1);
v_options_863_ = lean_ctor_get(v_toCold_858_, 2);
v___x_864_ = lean_box(v_suppressElabErrors_860_);
v___x_865_ = lean_box(v___y_857_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_866_, 0, v___x_864_);
lean_closure_set(v___f_866_, 1, v___x_865_);
v___x_867_ = 1;
v___x_868_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_867_);
if (v___x_868_ == 0)
{
v___y_849_ = v_fileMap_862_;
v___y_850_ = v___f_866_;
v___y_851_ = v_fileName_861_;
v___y_852_ = v___y_857_;
v___y_853_ = v_ref_859_;
v___y_854_ = v_suppressElabErrors_860_;
v___y_855_ = v___x_868_;
goto v___jp_848_;
}
else
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = l_Lean_warningAsError;
v___x_870_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_863_, v___x_869_);
v___y_849_ = v_fileMap_862_;
v___y_850_ = v___f_866_;
v___y_851_ = v_fileName_861_;
v___y_852_ = v___y_857_;
v___y_853_ = v_ref_859_;
v___y_854_ = v_suppressElabErrors_860_;
v___y_855_ = v___x_870_;
goto v___jp_848_;
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_msgData_754_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_875_, lean_object* v_msgData_876_, lean_object* v_severity_877_, lean_object* v_isSilent_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_severity_boxed_884_; uint8_t v_isSilent_boxed_885_; lean_object* v_res_886_; 
v_severity_boxed_884_ = lean_unbox(v_severity_877_);
v_isSilent_boxed_885_ = lean_unbox(v_isSilent_878_);
v_res_886_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_875_, v_msgData_876_, v_severity_boxed_884_, v_isSilent_boxed_885_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_ref_875_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_887_, lean_object* v_msgData_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; 
v___x_896_ = 1;
v___x_897_ = 0;
v___x_898_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_887_, v_msgData_888_, v___x_896_, v___x_897_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_899_, lean_object* v_msgData_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_899_, v_msgData_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v_ref_899_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_917_, lean_object* v_as_918_, size_t v_i_919_, size_t v_stop_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_a_930_; uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_919_, v_stop_920_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v_name_936_; lean_object* v_stx_937_; uint8_t v___y_939_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_935_ = lean_array_uget_borrowed(v_as_918_, v_i_919_);
v_name_936_ = lean_ctor_get(v___x_935_, 0);
v_stx_937_ = lean_ctor_get(v___x_935_, 1);
v___x_949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_950_ = lean_name_eq(v_name_936_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_952_ = lean_name_eq(v_name_936_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_box(0);
v_a_930_ = v___x_953_;
goto v___jp_929_;
}
else
{
v___y_939_ = v___x_952_;
goto v___jp_938_;
}
}
else
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_nat_dec_lt(v___x_954_, v___x_917_);
v___y_939_ = v___x_955_;
goto v___jp_938_;
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_936_);
v___x_941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_936_, v___y_939_);
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
v___x_946_ = l_Lean_MessageData_ofFormat(v___x_945_);
v___x_947_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_937_, v___x_946_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v_a_930_ = v_a_948_;
goto v___jp_929_;
}
else
{
return v___x_947_;
}
}
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_921_);
return v___x_956_;
}
v___jp_929_:
{
size_t v___x_931_; size_t v___x_932_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_919_, v___x_931_);
v_i_919_ = v___x_932_;
v_b_921_ = v_a_930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_stop_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_i_boxed_969_; size_t v_stop_boxed_970_; lean_object* v_res_971_; 
v_i_boxed_969_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_stop_boxed_970_ = lean_unbox_usize(v_stop_960_);
lean_dec(v_stop_960_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_957_, v_as_958_, v_i_boxed_969_, v_stop_boxed_970_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
lean_dec(v___x_957_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_972_, lean_object* v_as_973_, size_t v_i_974_, size_t v_stop_975_, lean_object* v_b_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_a_985_; lean_object* v___y_990_; uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_eq(v_i_974_, v_stop_975_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v_modifiers_994_; lean_object* v_attrs_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_993_ = lean_array_uget_borrowed(v_as_973_, v_i_974_);
v_modifiers_994_ = lean_ctor_get(v___x_993_, 2);
v_attrs_995_ = lean_ctor_get(v_modifiers_994_, 2);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_array_get_size(v_attrs_995_);
v___x_998_ = lean_box(0);
v___x_999_ = lean_nat_dec_lt(v___x_996_, v___x_997_);
if (v___x_999_ == 0)
{
v_a_985_ = v___x_998_;
goto v___jp_984_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_le(v___x_997_, v___x_997_);
if (v___x_1000_ == 0)
{
if (v___x_999_ == 0)
{
v_a_985_ = v___x_998_;
goto v___jp_984_;
}
else
{
size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = lean_usize_of_nat(v___x_997_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_972_, v_attrs_995_, v___x_1001_, v___x_1002_, v___x_998_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
v___y_990_ = v___x_1003_;
goto v___jp_989_;
}
}
else
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_997_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_972_, v_attrs_995_, v___x_1004_, v___x_1005_, v___x_998_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
v___y_990_ = v___x_1006_;
goto v___jp_989_;
}
}
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_b_976_);
return v___x_1007_;
}
v___jp_984_:
{
size_t v___x_986_; size_t v___x_987_; 
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_974_, v___x_986_);
v_i_974_ = v___x_987_;
v_b_976_ = v_a_985_;
goto _start;
}
v___jp_989_:
{
if (lean_obj_tag(v___y_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___y_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___y_990_, 1);
v_a_985_ = v_a_991_;
goto v___jp_984_;
}
else
{
return v___y_990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_stop_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v_i_boxed_1020_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1011_);
lean_dec(v_stop_1011_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1008_, v_as_1009_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_as_1009_);
lean_dec(v___x_1008_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_bs_1025_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_lt(v_i_1024_, v_sz_1023_);
if (v___x_1026_ == 0)
{
return v_bs_1025_;
}
else
{
lean_object* v_v_1027_; lean_object* v_termination_1028_; lean_object* v_decreasingBy_x3f_1029_; lean_object* v___x_1030_; lean_object* v_bs_x27_1031_; size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v_v_1027_ = lean_array_uget_borrowed(v_bs_1025_, v_i_1024_);
v_termination_1028_ = lean_ctor_get(v_v_1027_, 8);
v_decreasingBy_x3f_1029_ = lean_ctor_get(v_termination_1028_, 4);
lean_inc(v_decreasingBy_x3f_1029_);
v___x_1030_ = lean_unsigned_to_nat(0u);
v_bs_x27_1031_ = lean_array_uset(v_bs_1025_, v_i_1024_, v___x_1030_);
v___x_1032_ = ((size_t)1ULL);
v___x_1033_ = lean_usize_add(v_i_1024_, v___x_1032_);
v___x_1034_ = lean_array_uset(v_bs_x27_1031_, v_i_1024_, v_decreasingBy_x3f_1029_);
v_i_1024_ = v___x_1033_;
v_bs_1025_ = v___x_1034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1036_, lean_object* v_i_1037_, lean_object* v_bs_1038_){
_start:
{
size_t v_sz_boxed_1039_; size_t v_i_boxed_1040_; lean_object* v_res_1041_; 
v_sz_boxed_1039_ = lean_unbox_usize(v_sz_1036_);
lean_dec(v_sz_1036_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1039_, v_i_boxed_1040_, v_bs_1038_);
return v_res_1041_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1042_; double v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_float_of_nat(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_ref_1053_; lean_object* v___x_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1099_; 
v_ref_1053_ = lean_ctor_get(v___y_1050_, 2);
v___x_1054_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1099_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1099_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v_traceState_1060_; lean_object* v_env_1061_; lean_object* v_nextMacroScope_1062_; lean_object* v_ngen_1063_; lean_object* v_auxDeclNGen_1064_; lean_object* v_cache_1065_; lean_object* v_messages_1066_; lean_object* v_infoState_1067_; lean_object* v_snapshotTasks_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1098_; 
v___x_1059_ = lean_st_ref_take(v___y_1051_);
v_traceState_1060_ = lean_ctor_get(v___x_1059_, 4);
v_env_1061_ = lean_ctor_get(v___x_1059_, 0);
v_nextMacroScope_1062_ = lean_ctor_get(v___x_1059_, 1);
v_ngen_1063_ = lean_ctor_get(v___x_1059_, 2);
v_auxDeclNGen_1064_ = lean_ctor_get(v___x_1059_, 3);
v_cache_1065_ = lean_ctor_get(v___x_1059_, 5);
v_messages_1066_ = lean_ctor_get(v___x_1059_, 6);
v_infoState_1067_ = lean_ctor_get(v___x_1059_, 7);
v_snapshotTasks_1068_ = lean_ctor_get(v___x_1059_, 8);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1070_ = v___x_1059_;
v_isShared_1071_ = v_isSharedCheck_1098_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snapshotTasks_1068_);
lean_inc(v_infoState_1067_);
lean_inc(v_messages_1066_);
lean_inc(v_cache_1065_);
lean_inc(v_traceState_1060_);
lean_inc(v_auxDeclNGen_1064_);
lean_inc(v_ngen_1063_);
lean_inc(v_nextMacroScope_1062_);
lean_inc(v_env_1061_);
lean_dec(v___x_1059_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1098_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint64_t v_tid_1072_; lean_object* v_traces_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1097_; 
v_tid_1072_ = lean_ctor_get_uint64(v_traceState_1060_, sizeof(void*)*1);
v_traces_1073_ = lean_ctor_get(v_traceState_1060_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_traceState_1060_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1075_ = v_traceState_1060_;
v_isShared_1076_ = v_isSharedCheck_1097_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_traces_1073_);
lean_dec(v_traceState_1060_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1097_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; double v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1079_ = 0;
v___x_1080_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1081_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1081_, 0, v_cls_1046_);
lean_ctor_set(v___x_1081_, 1, v___x_1077_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
lean_ctor_set_float(v___x_1081_, sizeof(void*)*3, v___x_1078_);
lean_ctor_set_float(v___x_1081_, sizeof(void*)*3 + 8, v___x_1078_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*3 + 16, v___x_1079_);
v___x_1082_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1083_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v_a_1055_);
lean_ctor_set(v___x_1083_, 2, v___x_1082_);
lean_inc(v_ref_1053_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_ref_1053_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_PersistentArray_push___redArg(v_traces_1073_, v___x_1084_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1085_);
v___x_1087_ = v___x_1075_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1085_);
lean_ctor_set_uint64(v_reuseFailAlloc_1096_, sizeof(void*)*1, v_tid_1072_);
v___x_1087_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 4, v___x_1087_);
v___x_1089_ = v___x_1070_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_env_1061_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_nextMacroScope_1062_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_ngen_1063_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_auxDeclNGen_1064_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1095_, 5, v_cache_1065_);
lean_ctor_set(v_reuseFailAlloc_1095_, 6, v_messages_1066_);
lean_ctor_set(v_reuseFailAlloc_1095_, 7, v_infoState_1067_);
lean_ctor_set(v_reuseFailAlloc_1095_, 8, v_snapshotTasks_1068_);
v___x_1089_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = lean_st_ref_put(v___y_1051_, v___x_1089_);
v___x_1091_ = lean_box(0);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1091_);
v___x_1093_ = v___x_1057_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1100_, v_msg_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1111_, lean_object* v_snd_1112_, size_t v_sz_1113_, size_t v___x_1114_, lean_object* v_a_1115_, lean_object* v_fixedArgs_1116_, lean_object* v_fst_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v_wfRel_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v_a_1137_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v_toCold_1286_; lean_object* v_options_1287_; uint8_t v_hasTrace_1288_; 
v_toCold_1286_ = lean_ctor_get(v___y_1126_, 0);
v_options_1287_ = lean_ctor_get(v_toCold_1286_, 2);
v_hasTrace_1288_ = lean_ctor_get_uint8(v_options_1287_, sizeof(void*)*1);
if (v_hasTrace_1288_ == 0)
{
lean_dec(v___x_1120_);
v___y_1262_ = v___y_1122_;
v___y_1263_ = v___y_1123_;
v___y_1264_ = v___y_1124_;
v___y_1265_ = v___y_1125_;
v___y_1266_ = v___y_1126_;
v___y_1267_ = v___y_1127_;
goto v___jp_1261_;
}
else
{
lean_object* v_inheritedTraceOptions_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_inheritedTraceOptions_1289_ = lean_ctor_get(v_toCold_1286_, 11);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__1___closed__1));
lean_inc(v___x_1120_);
v___x_1291_ = l_Lean_Name_append(v___x_1290_, v___x_1120_);
v___x_1292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1289_, v_options_1287_, v___x_1291_);
lean_dec(v___x_1291_);
if (v___x_1292_ == 0)
{
lean_dec(v___x_1120_);
v___y_1262_ = v___y_1122_;
v___y_1263_ = v___y_1123_;
v___y_1264_ = v___y_1124_;
v___y_1265_ = v___y_1125_;
v___y_1266_ = v___y_1126_;
v___y_1267_ = v___y_1127_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1121_);
v___x_1294_ = l_Lean_MessageData_ofExpr(v_wfRel_1121_);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1120_, v___x_1295_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref_known(v___x_1296_, 1);
v___y_1262_ = v___y_1122_;
v___y_1263_ = v___y_1123_;
v___y_1264_ = v___y_1124_;
v___y_1265_ = v___y_1125_;
v___y_1266_ = v___y_1126_;
v___y_1267_ = v___y_1127_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_wfRel_1121_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_fst_1117_);
lean_dec_ref(v_fixedArgs_1116_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_fst_1111_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
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
v___jp_1129_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v___x_1138_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1136_, v___y_1133_, v___y_1134_);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1146_);
v___x_1140_ = v___x_1138_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v___x_1138_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 1);
lean_ctor_set(v___x_1140_, 0, v_a_1137_);
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1137_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
v___jp_1147_:
{
if (lean_obj_tag(v___y_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v___x_1160_; 
v_a_1156_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___y_1155_, 1);
v___x_1157_ = lean_st_ref_get(v___y_1152_);
v___x_1158_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1154_, v___y_1151_, v___y_1152_);
lean_dec_ref(v___x_1158_);
v_env_1159_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref_n(v_env_1159_, 2);
lean_dec(v___x_1157_);
v___x_1160_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1159_, v_a_1156_, v___y_1153_, v___y_1152_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1220_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1220_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1220_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v_env_1166_; lean_object* v_nextMacroScope_1167_; lean_object* v_ngen_1168_; lean_object* v_auxDeclNGen_1169_; lean_object* v_traceState_1170_; lean_object* v_messages_1171_; lean_object* v_infoState_1172_; lean_object* v_snapshotTasks_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1218_; 
v___x_1165_ = lean_st_ref_take(v___y_1152_);
v_env_1166_ = lean_ctor_get(v___x_1165_, 0);
v_nextMacroScope_1167_ = lean_ctor_get(v___x_1165_, 1);
v_ngen_1168_ = lean_ctor_get(v___x_1165_, 2);
v_auxDeclNGen_1169_ = lean_ctor_get(v___x_1165_, 3);
v_traceState_1170_ = lean_ctor_get(v___x_1165_, 4);
v_messages_1171_ = lean_ctor_get(v___x_1165_, 6);
v_infoState_1172_ = lean_ctor_get(v___x_1165_, 7);
v_snapshotTasks_1173_ = lean_ctor_get(v___x_1165_, 8);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1165_, 5);
lean_dec(v_unused_1219_);
v___x_1175_ = v___x_1165_;
v_isShared_1176_ = v_isSharedCheck_1218_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snapshotTasks_1173_);
lean_inc(v_infoState_1172_);
lean_inc(v_messages_1171_);
lean_inc(v_traceState_1170_);
lean_inc(v_auxDeclNGen_1169_);
lean_inc(v_ngen_1168_);
lean_inc(v_nextMacroScope_1167_);
lean_inc(v_env_1166_);
lean_dec(v___x_1165_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1218_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1177_ = l_Lean_copyExtraModUses(v_env_1159_, v_env_1166_);
v___x_1178_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 5, v___x_1178_);
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_nextMacroScope_1167_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_ngen_1168_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_auxDeclNGen_1169_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_traceState_1170_);
lean_ctor_set(v_reuseFailAlloc_1217_, 5, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_messages_1171_);
lean_ctor_set(v_reuseFailAlloc_1217_, 7, v_infoState_1172_);
lean_ctor_set(v_reuseFailAlloc_1217_, 8, v_snapshotTasks_1173_);
v___x_1180_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_mctx_1183_; lean_object* v_zetaDeltaFVarIds_1184_; lean_object* v_postponed_1185_; lean_object* v_diag_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1215_; 
v___x_1181_ = lean_st_ref_put(v___y_1152_, v___x_1180_);
v___x_1182_ = lean_st_ref_take(v___y_1151_);
v_mctx_1183_ = lean_ctor_get(v___x_1182_, 0);
v_zetaDeltaFVarIds_1184_ = lean_ctor_get(v___x_1182_, 2);
v_postponed_1185_ = lean_ctor_get(v___x_1182_, 3);
v_diag_1186_ = lean_ctor_get(v___x_1182_, 4);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1182_, 1);
lean_dec(v_unused_1216_);
v___x_1188_ = v___x_1182_;
v_isShared_1189_ = v_isSharedCheck_1215_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_diag_1186_);
lean_inc(v_postponed_1185_);
lean_inc(v_zetaDeltaFVarIds_1184_);
lean_inc(v_mctx_1183_);
lean_dec(v___x_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1215_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_mctx_1183_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_zetaDeltaFVarIds_1184_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_postponed_1185_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_diag_1186_);
v___x_1192_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v_ref_1194_; uint8_t v_kind_1195_; lean_object* v_levelParams_1196_; lean_object* v_modifiers_1197_; lean_object* v_declName_1198_; lean_object* v_binders_1199_; lean_object* v_numSectionVars_1200_; lean_object* v_type_1201_; lean_object* v_termination_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v___x_1193_ = lean_st_ref_put(v___y_1151_, v___x_1192_);
v_ref_1194_ = lean_ctor_get(v_fst_1111_, 0);
v_kind_1195_ = lean_ctor_get_uint8(v_fst_1111_, sizeof(void*)*9);
v_levelParams_1196_ = lean_ctor_get(v_fst_1111_, 1);
v_modifiers_1197_ = lean_ctor_get(v_fst_1111_, 2);
v_declName_1198_ = lean_ctor_get(v_fst_1111_, 3);
v_binders_1199_ = lean_ctor_get(v_fst_1111_, 4);
v_numSectionVars_1200_ = lean_ctor_get(v_fst_1111_, 5);
v_type_1201_ = lean_ctor_get(v_fst_1111_, 6);
v_termination_1202_ = lean_ctor_get(v_fst_1111_, 8);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_fst_1111_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_fst_1111_, 7);
lean_dec(v_unused_1213_);
v___x_1204_ = v_fst_1111_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_termination_1202_);
lean_inc(v_type_1201_);
lean_inc(v_numSectionVars_1200_);
lean_inc(v_binders_1199_);
lean_inc(v_declName_1198_);
lean_inc(v_modifiers_1197_);
lean_inc(v_levelParams_1196_);
lean_inc(v_ref_1194_);
lean_dec(v_fst_1111_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 7, v_a_1161_);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_ref_1194_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_levelParams_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_modifiers_1197_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_declName_1198_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_binders_1199_);
lean_ctor_set(v_reuseFailAlloc_1211_, 5, v_numSectionVars_1200_);
lean_ctor_set(v_reuseFailAlloc_1211_, 6, v_type_1201_);
lean_ctor_set(v_reuseFailAlloc_1211_, 7, v_a_1161_);
lean_ctor_set(v_reuseFailAlloc_1211_, 8, v_termination_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*9, v_kind_1195_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1207_);
v___x_1209_ = v___x_1163_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
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
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_env_1159_);
lean_dec_ref(v_fst_1111_);
v_a_1221_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1160_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1160_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; 
lean_dec_ref(v_fst_1111_);
v_a_1229_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___y_1155_, 1);
v___y_1130_ = v___y_1148_;
v___y_1131_ = v___y_1149_;
v___y_1132_ = v___y_1150_;
v___y_1133_ = v___y_1151_;
v___y_1134_ = v___y_1152_;
v___y_1135_ = v___y_1153_;
v___y_1136_ = v___y_1154_;
v_a_1137_ = v_a_1229_;
goto v___jp_1129_;
}
}
v___jp_1230_:
{
lean_object* v___x_1237_; lean_object* v_env_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_st_ref_get(v___y_1236_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc_ref(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1239_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1112_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1113_, v___x_1114_, v_a_1115_);
lean_inc_ref(v_fst_1111_);
v___x_1241_ = l_Lean_Elab_WF_mkFix(v_fst_1111_, v_fixedArgs_1116_, v_fst_1117_, v_wfRel_1121_, v___x_1118_, v___x_1240_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1242_, v___y_1235_, v___y_1236_);
v___y_1148_ = v___y_1231_;
v___y_1149_ = v___y_1233_;
v___y_1150_ = v___y_1232_;
v___y_1151_ = v___y_1234_;
v___y_1152_ = v___y_1236_;
v___y_1153_ = v___y_1235_;
v___y_1154_ = v_env_1238_;
v___y_1155_ = v___x_1243_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v___y_1231_;
v___y_1149_ = v___y_1233_;
v___y_1150_ = v___y_1232_;
v___y_1151_ = v___y_1234_;
v___y_1152_ = v___y_1236_;
v___y_1153_ = v___y_1235_;
v___y_1154_ = v_env_1238_;
v___y_1155_ = v___x_1241_;
goto v___jp_1147_;
}
}
else
{
lean_object* v_a_1244_; 
lean_dec_ref(v_wfRel_1121_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_fst_1117_);
lean_dec_ref(v_fixedArgs_1116_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_fst_1111_);
v_a_1244_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1239_, 1);
v___y_1130_ = v___y_1231_;
v___y_1131_ = v___y_1233_;
v___y_1132_ = v___y_1232_;
v___y_1133_ = v___y_1234_;
v___y_1134_ = v___y_1236_;
v___y_1135_ = v___y_1235_;
v___y_1136_ = v_env_1238_;
v_a_1137_ = v_a_1244_;
goto v___jp_1129_;
}
}
v___jp_1245_:
{
if (lean_obj_tag(v___y_1252_) == 0)
{
lean_dec_ref_known(v___y_1252_, 1);
v___y_1231_ = v___y_1248_;
v___y_1232_ = v___y_1251_;
v___y_1233_ = v___y_1249_;
v___y_1234_ = v___y_1246_;
v___y_1235_ = v___y_1250_;
v___y_1236_ = v___y_1247_;
goto v___jp_1230_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_wfRel_1121_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_fst_1117_);
lean_dec_ref(v_fixedArgs_1116_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_fst_1111_);
v_a_1253_ = lean_ctor_get(v___y_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___y_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___y_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___y_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
v___jp_1261_:
{
lean_object* v___x_1268_; 
lean_inc_ref(v_wfRel_1121_);
v___x_1268_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1121_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
if (lean_obj_tag(v_a_1269_) == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_a_1115_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1267_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_le(v___x_1271_, v___x_1271_);
if (v___x_1273_ == 0)
{
if (v___x_1272_ == 0)
{
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1267_;
goto v___jp_1230_;
}
else
{
size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_usize_of_nat(v___x_1271_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1271_, v_a_1115_, v___x_1114_, v___x_1274_, v___x_1119_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
v___y_1246_ = v___y_1265_;
v___y_1247_ = v___y_1267_;
v___y_1248_ = v___y_1262_;
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v___y_1251_ = v___y_1263_;
v___y_1252_ = v___x_1275_;
goto v___jp_1245_;
}
}
else
{
size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_usize_of_nat(v___x_1271_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1271_, v_a_1115_, v___x_1114_, v___x_1276_, v___x_1119_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
v___y_1246_ = v___y_1265_;
v___y_1247_ = v___y_1267_;
v___y_1248_ = v___y_1262_;
v___y_1249_ = v___y_1264_;
v___y_1250_ = v___y_1266_;
v___y_1251_ = v___y_1263_;
v___y_1252_ = v___x_1277_;
goto v___jp_1245_;
}
}
}
else
{
lean_dec_ref_known(v_a_1269_, 1);
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1267_;
goto v___jp_1230_;
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_wfRel_1121_);
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_fst_1117_);
lean_dec_ref(v_fixedArgs_1116_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_fst_1111_);
v_a_1278_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1268_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1268_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1305_ = _args[0];
lean_object* v_snd_1306_ = _args[1];
lean_object* v_sz_1307_ = _args[2];
lean_object* v___x_1308_ = _args[3];
lean_object* v_a_1309_ = _args[4];
lean_object* v_fixedArgs_1310_ = _args[5];
lean_object* v_fst_1311_ = _args[6];
lean_object* v___x_1312_ = _args[7];
lean_object* v___x_1313_ = _args[8];
lean_object* v___x_1314_ = _args[9];
lean_object* v_wfRel_1315_ = _args[10];
lean_object* v___y_1316_ = _args[11];
lean_object* v___y_1317_ = _args[12];
lean_object* v___y_1318_ = _args[13];
lean_object* v___y_1319_ = _args[14];
lean_object* v___y_1320_ = _args[15];
lean_object* v___y_1321_ = _args[16];
lean_object* v___y_1322_ = _args[17];
_start:
{
size_t v_sz_boxed_1323_; size_t v___x_44709__boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v___x_44709__boxed_1324_ = lean_unbox_usize(v___x_1308_);
lean_dec(v___x_1308_);
v_res_1325_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1305_, v_snd_1306_, v_sz_boxed_1323_, v___x_44709__boxed_1324_, v_a_1309_, v_fixedArgs_1310_, v_fst_1311_, v___x_1312_, v___x_1313_, v___x_1314_, v_wfRel_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v_snd_1306_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1329_, size_t v___x_1330_, lean_object* v_a_1331_, lean_object* v_fst_1332_, lean_object* v_snd_1333_, lean_object* v_fst_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v_declName_1337_, lean_object* v_fst_1338_, lean_object* v_wf_1339_, lean_object* v_fixedArgs_1340_, lean_object* v_type_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_whnfForall(v_type_1341_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; uint8_t v___x_1364_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1364_ = l_Lean_Expr_isForall(v_a_1350_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_fixedArgs_1340_);
lean_dec_ref(v_wf_1339_);
lean_dec_ref(v_fst_1338_);
lean_dec(v_declName_1337_);
lean_dec(v___x_1336_);
lean_dec_ref(v_fst_1334_);
lean_dec_ref(v_snd_1333_);
lean_dec_ref(v_fst_1332_);
lean_dec_ref(v_a_1331_);
v___x_1365_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1366_ = l_Lean_MessageData_ofExpr(v_a_1350_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1367_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
v___y_1352_ = v___y_1342_;
v___y_1353_ = v___y_1343_;
v___y_1354_ = v___y_1344_;
v___y_1355_ = v___y_1345_;
v___y_1356_ = v___y_1346_;
v___y_1357_ = v___y_1347_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; 
v___x_1358_ = l_Lean_Expr_bindingDomain_x21(v_a_1350_);
lean_dec(v_a_1350_);
lean_inc_ref(v_a_1331_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1329_, v___x_1330_, v_a_1331_);
v___x_1360_ = lean_box_usize(v_sz_1329_);
v___x_1361_ = lean_box_usize(v___x_1330_);
lean_inc_ref(v___x_1359_);
lean_inc_ref(v_fst_1334_);
lean_inc_ref(v_fixedArgs_1340_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1362_, 0, v_fst_1332_);
lean_closure_set(v___f_1362_, 1, v_snd_1333_);
lean_closure_set(v___f_1362_, 2, v___x_1360_);
lean_closure_set(v___f_1362_, 3, v___x_1361_);
lean_closure_set(v___f_1362_, 4, v_a_1331_);
lean_closure_set(v___f_1362_, 5, v_fixedArgs_1340_);
lean_closure_set(v___f_1362_, 6, v_fst_1334_);
lean_closure_set(v___f_1362_, 7, v___x_1359_);
lean_closure_set(v___f_1362_, 8, v___x_1335_);
lean_closure_set(v___f_1362_, 9, v___x_1336_);
v___x_1363_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1359_, v_declName_1337_, v_fst_1338_, v_fixedArgs_1340_, v_fst_1334_, v___x_1358_, v_wf_1339_, v___f_1362_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1363_;
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_fixedArgs_1340_);
lean_dec_ref(v_wf_1339_);
lean_dec_ref(v_fst_1338_);
lean_dec(v_declName_1337_);
lean_dec(v___x_1336_);
lean_dec_ref(v_fst_1334_);
lean_dec_ref(v_snd_1333_);
lean_dec_ref(v_fst_1332_);
lean_dec_ref(v_a_1331_);
v_a_1377_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1349_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1349_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1385_ = _args[0];
lean_object* v___x_1386_ = _args[1];
lean_object* v_a_1387_ = _args[2];
lean_object* v_fst_1388_ = _args[3];
lean_object* v_snd_1389_ = _args[4];
lean_object* v_fst_1390_ = _args[5];
lean_object* v___x_1391_ = _args[6];
lean_object* v___x_1392_ = _args[7];
lean_object* v_declName_1393_ = _args[8];
lean_object* v_fst_1394_ = _args[9];
lean_object* v_wf_1395_ = _args[10];
lean_object* v_fixedArgs_1396_ = _args[11];
lean_object* v_type_1397_ = _args[12];
lean_object* v___y_1398_ = _args[13];
lean_object* v___y_1399_ = _args[14];
lean_object* v___y_1400_ = _args[15];
lean_object* v___y_1401_ = _args[16];
lean_object* v___y_1402_ = _args[17];
lean_object* v___y_1403_ = _args[18];
lean_object* v___y_1404_ = _args[19];
_start:
{
size_t v_sz_boxed_1405_; size_t v___x_45067__boxed_1406_; lean_object* v_res_1407_; 
v_sz_boxed_1405_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v___x_45067__boxed_1406_ = lean_unbox_usize(v___x_1386_);
lean_dec(v___x_1386_);
v_res_1407_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1405_, v___x_45067__boxed_1406_, v_a_1387_, v_fst_1388_, v_snd_1389_, v_fst_1390_, v___x_1391_, v___x_1392_, v_declName_1393_, v_fst_1394_, v_wf_1395_, v_fixedArgs_1396_, v_type_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1408_, lean_object* v_fst_1409_, lean_object* v_fst_1410_, lean_object* v_fst_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Elab_WF_guessLex(v_a_1408_, v_fst_1409_, v_fst_1410_, v_fst_1411_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1420_, lean_object* v_fst_1421_, lean_object* v_fst_1422_, lean_object* v_fst_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1420_, v_fst_1421_, v_fst_1422_, v_fst_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1432_, uint8_t v_isExporting_1433_, lean_object* v___x_1434_, lean_object* v___y_1435_, lean_object* v___x_1436_, lean_object* v_a_x3f_1437_){
_start:
{
lean_object* v___x_1439_; lean_object* v_env_1440_; lean_object* v_nextMacroScope_1441_; lean_object* v_ngen_1442_; lean_object* v_auxDeclNGen_1443_; lean_object* v_traceState_1444_; lean_object* v_messages_1445_; lean_object* v_infoState_1446_; lean_object* v_snapshotTasks_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1472_; 
v___x_1439_ = lean_st_ref_take(v___y_1432_);
v_env_1440_ = lean_ctor_get(v___x_1439_, 0);
v_nextMacroScope_1441_ = lean_ctor_get(v___x_1439_, 1);
v_ngen_1442_ = lean_ctor_get(v___x_1439_, 2);
v_auxDeclNGen_1443_ = lean_ctor_get(v___x_1439_, 3);
v_traceState_1444_ = lean_ctor_get(v___x_1439_, 4);
v_messages_1445_ = lean_ctor_get(v___x_1439_, 6);
v_infoState_1446_ = lean_ctor_get(v___x_1439_, 7);
v_snapshotTasks_1447_ = lean_ctor_get(v___x_1439_, 8);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v___x_1439_, 5);
lean_dec(v_unused_1473_);
v___x_1449_ = v___x_1439_;
v_isShared_1450_ = v_isSharedCheck_1472_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_snapshotTasks_1447_);
lean_inc(v_infoState_1446_);
lean_inc(v_messages_1445_);
lean_inc(v_traceState_1444_);
lean_inc(v_auxDeclNGen_1443_);
lean_inc(v_ngen_1442_);
lean_inc(v_nextMacroScope_1441_);
lean_inc(v_env_1440_);
lean_dec(v___x_1439_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1472_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lean_Environment_setExporting(v_env_1440_, v_isExporting_1433_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 5, v___x_1434_);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_nextMacroScope_1441_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_ngen_1442_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_auxDeclNGen_1443_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v_traceState_1444_);
lean_ctor_set(v_reuseFailAlloc_1471_, 5, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1471_, 6, v_messages_1445_);
lean_ctor_set(v_reuseFailAlloc_1471_, 7, v_infoState_1446_);
lean_ctor_set(v_reuseFailAlloc_1471_, 8, v_snapshotTasks_1447_);
v___x_1453_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_mctx_1456_; lean_object* v_zetaDeltaFVarIds_1457_; lean_object* v_postponed_1458_; lean_object* v_diag_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1469_; 
v___x_1454_ = lean_st_ref_put(v___y_1432_, v___x_1453_);
v___x_1455_ = lean_st_ref_take(v___y_1435_);
v_mctx_1456_ = lean_ctor_get(v___x_1455_, 0);
v_zetaDeltaFVarIds_1457_ = lean_ctor_get(v___x_1455_, 2);
v_postponed_1458_ = lean_ctor_get(v___x_1455_, 3);
v_diag_1459_ = lean_ctor_get(v___x_1455_, 4);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1455_, 1);
lean_dec(v_unused_1470_);
v___x_1461_ = v___x_1455_;
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_diag_1459_);
lean_inc(v_postponed_1458_);
lean_inc(v_zetaDeltaFVarIds_1457_);
lean_inc(v_mctx_1456_);
lean_dec(v___x_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___x_1436_);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_mctx_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_zetaDeltaFVarIds_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_postponed_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_diag_1459_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_st_ref_put(v___y_1435_, v___x_1464_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1474_, lean_object* v_isExporting_1475_, lean_object* v___x_1476_, lean_object* v___y_1477_, lean_object* v___x_1478_, lean_object* v_a_x3f_1479_, lean_object* v___y_1480_){
_start:
{
uint8_t v_isExporting_boxed_1481_; lean_object* v_res_1482_; 
v_isExporting_boxed_1481_ = lean_unbox(v_isExporting_1475_);
v_res_1482_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1474_, v_isExporting_boxed_1481_, v___x_1476_, v___y_1477_, v___x_1478_, v_a_x3f_1479_);
lean_dec(v_a_x3f_1479_);
lean_dec(v___y_1477_);
lean_dec(v___y_1474_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1483_, uint8_t v_isExporting_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; lean_object* v___x_1494_; uint8_t v_isModule_1495_; 
v___x_1492_ = lean_st_ref_get(v___y_1490_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = l_Lean_Environment_header(v_env_1493_);
v_isModule_1495_ = lean_ctor_get_uint8(v___x_1494_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1494_);
if (v_isModule_1495_ == 0)
{
lean_object* v___x_1496_; 
lean_dec_ref(v_env_1493_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v___x_1496_ = lean_apply_7(v_x_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, lean_box(0));
return v___x_1496_;
}
else
{
uint8_t v_isExporting_1497_; 
v_isExporting_1497_ = lean_ctor_get_uint8(v_env_1493_, sizeof(void*)*8);
lean_dec_ref(v_env_1493_);
if (v_isExporting_1484_ == 0)
{
if (v_isExporting_1497_ == 0)
{
lean_object* v___x_1563_; 
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v___x_1563_ = lean_apply_7(v_x_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, lean_box(0));
return v___x_1563_;
}
else
{
goto v___jp_1498_;
}
}
else
{
if (v_isExporting_1497_ == 0)
{
goto v___jp_1498_;
}
else
{
lean_object* v___x_1564_; 
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v___x_1564_ = lean_apply_7(v_x_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, lean_box(0));
return v___x_1564_;
}
}
v___jp_1498_:
{
lean_object* v___x_1499_; lean_object* v_env_1500_; lean_object* v_nextMacroScope_1501_; lean_object* v_ngen_1502_; lean_object* v_auxDeclNGen_1503_; lean_object* v_traceState_1504_; lean_object* v_messages_1505_; lean_object* v_infoState_1506_; lean_object* v_snapshotTasks_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1561_; 
v___x_1499_ = lean_st_ref_take(v___y_1490_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
v_nextMacroScope_1501_ = lean_ctor_get(v___x_1499_, 1);
v_ngen_1502_ = lean_ctor_get(v___x_1499_, 2);
v_auxDeclNGen_1503_ = lean_ctor_get(v___x_1499_, 3);
v_traceState_1504_ = lean_ctor_get(v___x_1499_, 4);
v_messages_1505_ = lean_ctor_get(v___x_1499_, 6);
v_infoState_1506_ = lean_ctor_get(v___x_1499_, 7);
v_snapshotTasks_1507_ = lean_ctor_get(v___x_1499_, 8);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1499_, 5);
lean_dec(v_unused_1562_);
v___x_1509_ = v___x_1499_;
v_isShared_1510_ = v_isSharedCheck_1561_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snapshotTasks_1507_);
lean_inc(v_infoState_1506_);
lean_inc(v_messages_1505_);
lean_inc(v_traceState_1504_);
lean_inc(v_auxDeclNGen_1503_);
lean_inc(v_ngen_1502_);
lean_inc(v_nextMacroScope_1501_);
lean_inc(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1561_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1511_ = l_Lean_Environment_setExporting(v_env_1500_, v_isExporting_1484_);
v___x_1512_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 5, v___x_1512_);
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_nextMacroScope_1501_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_ngen_1502_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_auxDeclNGen_1503_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_traceState_1504_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_messages_1505_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v_infoState_1506_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v_snapshotTasks_1507_);
v___x_1514_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_mctx_1517_; lean_object* v_zetaDeltaFVarIds_1518_; lean_object* v_postponed_1519_; lean_object* v_diag_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1558_; 
v___x_1515_ = lean_st_ref_put(v___y_1490_, v___x_1514_);
v___x_1516_ = lean_st_ref_take(v___y_1488_);
v_mctx_1517_ = lean_ctor_get(v___x_1516_, 0);
v_zetaDeltaFVarIds_1518_ = lean_ctor_get(v___x_1516_, 2);
v_postponed_1519_ = lean_ctor_get(v___x_1516_, 3);
v_diag_1520_ = lean_ctor_get(v___x_1516_, 4);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v___x_1516_, 1);
lean_dec(v_unused_1559_);
v___x_1522_ = v___x_1516_;
v_isShared_1523_ = v_isSharedCheck_1558_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_diag_1520_);
lean_inc(v_postponed_1519_);
lean_inc(v_zetaDeltaFVarIds_1518_);
lean_inc(v_mctx_1517_);
lean_dec(v___x_1516_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1558_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_mctx_1517_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_zetaDeltaFVarIds_1518_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_postponed_1519_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_diag_1520_);
v___x_1526_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v_r_1528_; 
v___x_1527_ = lean_st_ref_put(v___y_1488_, v___x_1526_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v_r_1528_ = lean_apply_7(v_x_1483_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, lean_box(0));
if (lean_obj_tag(v_r_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1545_; 
v_a_1529_ = lean_ctor_get(v_r_1528_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_r_1528_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1531_ = v_r_1528_;
v_isShared_1532_ = v_isSharedCheck_1545_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_r_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1545_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
lean_inc(v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v___x_1535_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1490_, v_isExporting_1497_, v___x_1512_, v___y_1488_, v___x_1524_, v___x_1534_);
lean_dec_ref(v___x_1534_);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v___x_1535_, 0);
lean_dec(v_unused_1543_);
v___x_1537_ = v___x_1535_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v___x_1535_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_a_1529_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1529_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1546_ = lean_ctor_get(v_r_1528_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v_r_1528_, 1);
v___x_1547_ = lean_box(0);
v___x_1548_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1490_, v_isExporting_1497_, v___x_1512_, v___y_1488_, v___x_1524_, v___x_1547_);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v___x_1548_, 0);
lean_dec(v_unused_1556_);
v___x_1550_ = v___x_1548_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v___x_1548_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 1);
lean_ctor_set(v___x_1550_, 0, v_a_1546_);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1546_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1565_, lean_object* v_isExporting_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v_isExporting_boxed_1574_; lean_object* v_res_1575_; 
v_isExporting_boxed_1574_ = lean_unbox(v_isExporting_1566_);
v_res_1575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1565_, v_isExporting_boxed_1574_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1576_, uint8_t v_when_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
if (v_when_1577_ == 0)
{
lean_object* v___x_1585_; 
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1585_ = lean_apply_7(v_x_1576_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
return v___x_1585_;
}
else
{
uint8_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = 0;
v___x_1587_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1576_, v___x_1586_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1588_, lean_object* v_when_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v_when_boxed_1597_; lean_object* v_res_1598_; 
v_when_boxed_1597_ = lean_unbox(v_when_1589_);
v_res_1598_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1588_, v_when_boxed_1597_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1599_, size_t v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1600_, v_sz_1599_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_bs_1601_);
return v___x_1606_;
}
else
{
lean_object* v_v_1607_; lean_object* v_ref_1608_; uint8_t v_kind_1609_; lean_object* v_levelParams_1610_; lean_object* v_modifiers_1611_; lean_object* v_declName_1612_; lean_object* v_binders_1613_; lean_object* v_numSectionVars_1614_; lean_object* v_type_1615_; lean_object* v_value_1616_; lean_object* v_termination_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1640_; 
v_v_1607_ = lean_array_uget(v_bs_1601_, v_i_1600_);
v_ref_1608_ = lean_ctor_get(v_v_1607_, 0);
v_kind_1609_ = lean_ctor_get_uint8(v_v_1607_, sizeof(void*)*9);
v_levelParams_1610_ = lean_ctor_get(v_v_1607_, 1);
v_modifiers_1611_ = lean_ctor_get(v_v_1607_, 2);
v_declName_1612_ = lean_ctor_get(v_v_1607_, 3);
v_binders_1613_ = lean_ctor_get(v_v_1607_, 4);
v_numSectionVars_1614_ = lean_ctor_get(v_v_1607_, 5);
v_type_1615_ = lean_ctor_get(v_v_1607_, 6);
v_value_1616_ = lean_ctor_get(v_v_1607_, 7);
v_termination_1617_ = lean_ctor_get(v_v_1607_, 8);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_v_1607_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1619_ = v_v_1607_;
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_termination_1617_);
lean_inc(v_value_1616_);
lean_inc(v_type_1615_);
lean_inc(v_numSectionVars_1614_);
lean_inc(v_binders_1613_);
lean_inc(v_declName_1612_);
lean_inc(v_modifiers_1611_);
lean_inc(v_levelParams_1610_);
lean_inc(v_ref_1608_);
lean_dec(v_v_1607_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Elab_WF_floatRecApp(v_value_1616_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v_bs_x27_1624_; lean_object* v___x_1626_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = lean_unsigned_to_nat(0u);
v_bs_x27_1624_ = lean_array_uset(v_bs_1601_, v_i_1600_, v___x_1623_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 7, v_a_1622_);
v___x_1626_ = v___x_1619_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_ref_1608_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_levelParams_1610_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_modifiers_1611_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_declName_1612_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_binders_1613_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v_numSectionVars_1614_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_type_1615_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v_a_1622_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_termination_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1631_, sizeof(void*)*9, v_kind_1609_);
v___x_1626_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_add(v_i_1600_, v___x_1627_);
v___x_1629_ = lean_array_uset(v_bs_x27_1624_, v_i_1600_, v___x_1626_);
v_i_1600_ = v___x_1628_;
v_bs_1601_ = v___x_1629_;
goto _start;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_del_object(v___x_1619_);
lean_dec_ref(v_termination_1617_);
lean_dec_ref(v_type_1615_);
lean_dec(v_numSectionVars_1614_);
lean_dec(v_binders_1613_);
lean_dec(v_declName_1612_);
lean_dec_ref(v_modifiers_1611_);
lean_dec(v_levelParams_1610_);
lean_dec(v_ref_1608_);
lean_dec_ref(v_bs_1601_);
v_a_1632_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1621_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1621_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1641_, lean_object* v_i_1642_, lean_object* v_bs_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
size_t v_sz_boxed_1647_; size_t v_i_boxed_1648_; lean_object* v_res_1649_; 
v_sz_boxed_1647_ = lean_unbox_usize(v_sz_1641_);
lean_dec(v_sz_1641_);
v_i_boxed_1648_ = lean_unbox_usize(v_i_1642_);
lean_dec(v_i_1642_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1647_, v_i_boxed_1648_, v_bs_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(size_t v_sz_1650_, size_t v_i_1651_, lean_object* v_bs_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_bs_1652_);
return v___x_1654_;
}
else
{
lean_object* v_v_1655_; 
v_v_1655_ = lean_array_uget_borrowed(v_bs_1652_, v_i_1651_);
if (lean_obj_tag(v_v_1655_) == 0)
{
lean_object* v___x_1656_; 
lean_dec_ref(v_bs_1652_);
v___x_1656_ = lean_box(0);
return v___x_1656_;
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1658_; lean_object* v_bs_x27_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_val_1657_ = lean_ctor_get(v_v_1655_, 0);
lean_inc(v_val_1657_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v_bs_x27_1659_ = lean_array_uset(v_bs_1652_, v_i_1651_, v___x_1658_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1651_, v___x_1660_);
v___x_1662_ = lean_array_uset(v_bs_x27_1659_, v_i_1651_, v_val_1657_);
v_i_1651_ = v___x_1661_;
v_bs_1652_ = v___x_1662_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_sz_1664_, lean_object* v_i_1665_, lean_object* v_bs_1666_){
_start:
{
size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1664_);
lean_dec(v_sz_1664_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1665_);
lean_dec(v_i_1665_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_1667_, v_i_boxed_1668_, v_bs_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_bs_1672_);
return v___x_1679_;
}
else
{
uint8_t v___x_1680_; lean_object* v_v_1681_; lean_object* v___x_1682_; 
v___x_1680_ = 0;
v_v_1681_ = lean_array_uget_borrowed(v_bs_1672_, v_i_1671_);
lean_inc(v_v_1681_);
v___x_1682_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1681_, v___x_1680_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v_bs_x27_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_bs_x27_1685_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1684_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1671_, v___x_1686_);
v___x_1688_ = lean_array_uset(v_bs_x27_1685_, v_i_1671_, v_a_1683_);
v_i_1671_ = v___x_1687_;
v_bs_1672_ = v___x_1688_;
goto _start;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_bs_1672_);
v_a_1690_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1682_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1682_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1698_, lean_object* v_i_1699_, lean_object* v_bs_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
size_t v_sz_boxed_1706_; size_t v_i_boxed_1707_; lean_object* v_res_1708_; 
v_sz_boxed_1706_ = lean_unbox_usize(v_sz_1698_);
lean_dec(v_sz_1698_);
v_i_boxed_1707_ = lean_unbox_usize(v_i_1699_);
lean_dec(v_i_1699_);
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1706_, v_i_boxed_1707_, v_bs_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1709_, lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_env_1719_; lean_object* v_a_1721_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1718_ = lean_st_ref_get(v___y_1716_);
v_env_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_env_1719_);
lean_dec(v___x_1718_);
v___x_1731_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1709_, v___y_1714_, v___y_1716_);
lean_dec_ref(v___x_1731_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
v___x_1732_ = lean_apply_7(v_x_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, lean_box(0));
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1719_, v___y_1714_, v___y_1716_);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1742_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1733_);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1733_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1732_, 1);
v_a_1721_ = v_a_1743_;
goto v___jp_1720_;
}
v___jp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v___x_1722_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1719_, v___y_1714_, v___y_1716_);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1722_, 0);
lean_dec(v_unused_1730_);
v___x_1724_ = v___x_1722_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v___x_1722_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 1);
lean_ctor_set(v___x_1724_, 0, v_a_1721_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1721_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1744_, v_x_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1754_, lean_object* v_as_1755_, size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_a_1765_; uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_lt(v_i_1757_, v_sz_1756_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec(v___x_1754_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1758_);
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; uint8_t v_kind_1772_; lean_object* v_declName_1773_; lean_object* v_type_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_a_1771_ = lean_array_uget_borrowed(v_as_1755_, v_i_1757_);
v_kind_1772_ = lean_ctor_get_uint8(v_a_1771_, sizeof(void*)*9);
v_declName_1773_ = lean_ctor_get(v_a_1771_, 3);
v_type_1774_ = lean_ctor_get(v_a_1771_, 6);
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_name_eq(v_declName_1773_, v___x_1754_);
if (v___x_1776_ == 0)
{
uint8_t v___x_1777_; 
v___x_1777_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1772_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_inc_ref(v_type_1774_);
v___x_1778_ = l_Lean_Meta_isProp(v_type_1774_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; uint8_t v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = lean_unbox(v_a_1779_);
lean_dec(v_a_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
lean_inc(v___x_1754_);
lean_inc(v_a_1771_);
v___x_1781_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1771_, v___x_1754_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_dec_ref_known(v___x_1781_, 1);
v_a_1765_ = v___x_1775_;
goto v___jp_1764_;
}
else
{
lean_dec(v___x_1754_);
return v___x_1781_;
}
}
else
{
v_a_1765_ = v___x_1775_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v___x_1754_);
v_a_1782_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1778_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
v_a_1765_ = v___x_1775_;
goto v___jp_1764_;
}
}
else
{
v_a_1765_ = v___x_1775_;
goto v___jp_1764_;
}
}
v___jp_1764_:
{
size_t v___x_1766_; size_t v___x_1767_; 
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1757_, v___x_1766_);
v_i_1757_ = v___x_1767_;
v_b_1758_ = v_a_1765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1790_, lean_object* v_as_1791_, lean_object* v_sz_1792_, lean_object* v_i_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1792_);
lean_dec(v_sz_1792_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1790_, v_as_1791_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v_as_1791_);
return v_res_1802_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1811_ = l_Lean_stringToMessageData(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1814_ = l_Lean_stringToMessageData(v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1820_ = l_Lean_stringToMessageData(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1823_, lean_object* v_preDefs_1824_, lean_object* v_termMeasure_x3fs_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
size_t v_sz_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v_sz_1833_ = lean_array_size(v_preDefs_1824_);
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1833_, v___x_1834_, v_preDefs_1824_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v_env_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; size_t v_sz_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_n(v_a_1836_, 2);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_st_ref_get(v_a_1831_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_env_1838_);
lean_dec(v___x_1837_);
v___x_1839_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1840_ = lean_box(0);
v_sz_1854_ = lean_array_size(v_a_1836_);
v___x_1855_ = lean_box_usize(v_sz_1854_);
v___x_1856_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1857_, 0, v_a_1836_);
lean_closure_set(v___f_1857_, 1, v___x_1855_);
lean_closure_set(v___f_1857_, 2, v___x_1856_);
lean_closure_set(v___f_1857_, 3, v___x_1840_);
lean_closure_set(v___f_1857_, 4, v___x_1839_);
v___x_1858_ = l_Lean_Environment_unlockAsync(v_env_1838_);
v___x_1859_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1858_, v___f_1857_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v_snd_1861_; lean_object* v_fst_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_2049_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v_snd_1861_ = lean_ctor_get(v_a_1860_, 1);
v_fst_1862_ = lean_ctor_get(v_a_1860_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_1860_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_1864_ = v_a_1860_;
v_isShared_1865_ = v_isSharedCheck_2049_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snd_1861_);
lean_inc(v_fst_1862_);
lean_dec(v_a_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_2049_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_2048_; 
v_fst_1866_ = lean_ctor_get(v_snd_1861_, 0);
v_snd_1867_ = lean_ctor_get(v_snd_1861_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_snd_1861_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_1869_ = v_snd_1861_;
v_isShared_1870_ = v_isSharedCheck_2048_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snd_1867_);
lean_inc(v_fst_1866_);
lean_dec(v_snd_1861_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_2048_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___x_1930_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_wf_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___f_1978_; size_t v_sz_1979_; lean_object* v_termMeasures_x3f_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; uint8_t v___x_2041_; 
v___x_1930_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1976_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1930_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
lean_inc(v_snd_1867_);
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1978_, 0, v_snd_1867_);
v_sz_1979_ = lean_array_size(v_termMeasure_x3fs_1825_);
v_termMeasures_x3f_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_1979_, v___x_1834_, v_termMeasure_x3fs_1825_);
v___x_2041_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_2041_ == 0)
{
v___y_2004_ = v_a_1826_;
v___y_2005_ = v_a_1827_;
v___y_2006_ = v_a_1828_;
v___y_2007_ = v_a_1829_;
v___y_2008_ = v_a_1830_;
v___y_2009_ = v_a_1831_;
goto v___jp_2003_;
}
else
{
lean_object* v_value_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_value_2042_ = lean_ctor_get(v_snd_1867_, 7);
v___x_2043_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2042_);
v___x_2044_ = l_Lean_MessageData_ofExpr(v_value_2042_);
v___x_2045_ = l_Lean_indentD(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2043_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1930_, v___x_2046_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_dec_ref_known(v___x_2047_, 1);
v___y_2004_ = v_a_1826_;
v___y_2005_ = v_a_1827_;
v___y_2006_ = v_a_1828_;
v___y_2007_ = v_a_1829_;
v___y_2008_ = v_a_1830_;
v___y_2009_ = v_a_1831_;
goto v___jp_2003_;
}
else
{
lean_dec(v_termMeasures_x3f_1980_);
lean_dec_ref(v___f_1978_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
return v___x_2047_;
}
}
v___jp_1871_:
{
lean_object* v___x_1881_; 
lean_inc_ref(v___y_1872_);
lean_inc(v_a_1836_);
lean_inc(v_fst_1866_);
lean_inc(v_fst_1862_);
v___x_1881_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1862_, v_fst_1866_, v_a_1836_, v___y_1872_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
lean_inc_ref(v___y_1872_);
lean_inc(v_a_1836_);
lean_inc_ref(v_docCtx_1823_);
v___x_1883_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1823_, v_a_1836_, v_a_1882_, v___y_1872_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v_a_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1883_, 1);
lean_inc(v_a_1836_);
v___x_1884_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1823_, v_a_1836_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref_known(v___x_1884_, 1);
v___x_1885_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1867_, v___y_1874_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1854_, v___x_1834_, v_a_1836_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v_declName_1889_; lean_object* v___x_1890_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_n(v_a_1888_, 2);
lean_dec_ref_known(v___x_1887_, 1);
v_declName_1889_ = lean_ctor_get(v___y_1872_, 3);
lean_inc_n(v_declName_1889_, 2);
lean_dec_ref(v___y_1872_);
v___x_1890_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1888_, v_declName_1889_, v_fst_1862_, v_fst_1866_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_declName_1891_; lean_object* v_type_1892_; lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1890_, 1);
v_declName_1891_ = lean_ctor_get(v_a_1886_, 3);
v_type_1892_ = lean_ctor_get(v_a_1886_, 6);
lean_inc(v_declName_1891_);
v___x_1893_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1891_, v___y_1880_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1893_, 1);
lean_inc_ref(v_type_1892_);
v___x_1894_ = l_Lean_Meta_isProp(v_type_1892_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; uint8_t v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = lean_unbox(v_a_1895_);
lean_dec(v_a_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_inc(v_declName_1889_);
v___x_1897_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1886_, v_declName_1889_, v___y_1873_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_dec_ref_known(v___x_1897_, 1);
v___y_1842_ = v_a_1888_;
v___y_1843_ = v_declName_1889_;
v___y_1844_ = v___y_1875_;
v___y_1845_ = v___y_1876_;
v___y_1846_ = v___y_1877_;
v___y_1847_ = v___y_1878_;
v___y_1848_ = v___y_1879_;
v___y_1849_ = v___y_1880_;
goto v___jp_1841_;
}
else
{
lean_dec(v_declName_1889_);
lean_dec(v_a_1888_);
return v___x_1897_;
}
}
else
{
lean_dec(v_a_1886_);
lean_dec_ref(v___y_1873_);
v___y_1842_ = v_a_1888_;
v___y_1843_ = v_declName_1889_;
v___y_1844_ = v___y_1875_;
v___y_1845_ = v___y_1876_;
v___y_1846_ = v___y_1877_;
v___y_1847_ = v___y_1878_;
v___y_1848_ = v___y_1879_;
v___y_1849_ = v___y_1880_;
goto v___jp_1841_;
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_declName_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1886_);
lean_dec_ref(v___y_1873_);
v_a_1898_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1894_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1894_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_dec(v_declName_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1886_);
lean_dec_ref(v___y_1873_);
return v___x_1893_;
}
}
else
{
lean_dec(v_declName_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1886_);
lean_dec_ref(v___y_1873_);
return v___x_1890_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1886_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
v_a_1906_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1887_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1887_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
v_a_1914_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1885_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1885_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
return v___x_1884_;
}
}
else
{
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
return v___x_1883_;
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
v_a_1922_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1881_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1881_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
v___jp_1931_:
{
lean_object* v_declName_1941_; lean_object* v_type_1942_; lean_object* v_numFixed_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; 
v_declName_1941_ = lean_ctor_get(v_snd_1867_, 3);
v_type_1942_ = lean_ctor_get(v_snd_1867_, 6);
v_numFixed_1943_ = lean_ctor_get(v_fst_1862_, 0);
v___x_1944_ = lean_box_usize(v_sz_1854_);
v___x_1945_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1862_);
lean_inc(v_declName_1941_);
lean_inc(v_fst_1866_);
lean_inc(v_snd_1867_);
lean_inc(v_a_1836_);
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1946_, 0, v___x_1944_);
lean_closure_set(v___f_1946_, 1, v___x_1945_);
lean_closure_set(v___f_1946_, 2, v_a_1836_);
lean_closure_set(v___f_1946_, 3, v___y_1932_);
lean_closure_set(v___f_1946_, 4, v_snd_1867_);
lean_closure_set(v___f_1946_, 5, v_fst_1866_);
lean_closure_set(v___f_1946_, 6, v___x_1840_);
lean_closure_set(v___f_1946_, 7, v___x_1930_);
lean_closure_set(v___f_1946_, 8, v_declName_1941_);
lean_closure_set(v___f_1946_, 9, v_fst_1862_);
lean_closure_set(v___f_1946_, 10, v_wf_1934_);
lean_inc(v_numFixed_1943_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_numFixed_1943_);
v___x_1948_ = 0;
lean_inc_ref(v_type_1942_);
v___x_1949_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1942_, v___x_1947_, v___f_1946_, v___x_1948_, v___x_1948_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v_a_1952_; uint8_t v___x_1953_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1930_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = lean_unbox(v_a_1952_);
lean_dec(v_a_1952_);
if (v___x_1953_ == 0)
{
lean_del_object(v___x_1869_);
lean_del_object(v___x_1864_);
v___y_1872_ = v_a_1950_;
v___y_1873_ = v___y_1933_;
v___y_1874_ = v___x_1948_;
v___y_1875_ = v___y_1935_;
v___y_1876_ = v___y_1936_;
v___y_1877_ = v___y_1937_;
v___y_1878_ = v___y_1938_;
v___y_1879_ = v___y_1939_;
v___y_1880_ = v___y_1940_;
goto v___jp_1871_;
}
else
{
lean_object* v_declName_1954_; lean_object* v_value_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v_declName_1954_ = lean_ctor_get(v_a_1950_, 3);
v_value_1955_ = lean_ctor_get(v_a_1950_, 7);
v___x_1956_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1954_);
v___x_1957_ = l_Lean_MessageData_ofName(v_declName_1954_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 7);
lean_ctor_set(v___x_1869_, 1, v___x_1957_);
lean_ctor_set(v___x_1869_, 0, v___x_1956_);
v___x_1959_ = v___x_1869_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 7);
lean_ctor_set(v___x_1864_, 1, v___x_1960_);
lean_ctor_set(v___x_1864_, 0, v___x_1959_);
v___x_1962_ = v___x_1864_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref(v_value_1955_);
v___x_1963_ = l_Lean_MessageData_ofExpr(v_value_1955_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1930_, v___x_1964_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
v___y_1872_ = v_a_1950_;
v___y_1873_ = v___y_1933_;
v___y_1874_ = v___x_1948_;
v___y_1875_ = v___y_1935_;
v___y_1876_ = v___y_1936_;
v___y_1877_ = v___y_1937_;
v___y_1878_ = v___y_1938_;
v___y_1879_ = v___y_1939_;
v___y_1880_ = v___y_1940_;
goto v___jp_1871_;
}
else
{
lean_dec(v_a_1950_);
lean_dec_ref(v___y_1933_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
return v___x_1965_;
}
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v___y_1933_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
v_a_1968_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1949_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1949_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
v___jp_1981_:
{
if (lean_obj_tag(v_termMeasures_x3f_1980_) == 1)
{
lean_object* v_val_1991_; 
lean_dec_ref(v___y_1984_);
v_val_1991_ = lean_ctor_get(v_termMeasures_x3f_1980_, 0);
lean_inc(v_val_1991_);
lean_dec_ref_known(v_termMeasures_x3f_1980_, 1);
v___y_1932_ = v___y_1982_;
v___y_1933_ = v___y_1983_;
v_wf_1934_ = v_val_1991_;
v___y_1935_ = v___y_1985_;
v___y_1936_ = v___y_1986_;
v___y_1937_ = v___y_1987_;
v___y_1938_ = v___y_1988_;
v___y_1939_ = v___y_1989_;
v___y_1940_ = v___y_1990_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1992_; lean_object* v___x_1993_; 
lean_dec(v_termMeasures_x3f_1980_);
v___x_1992_ = 1;
v___x_1993_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1984_, v___x_1992_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___y_1932_ = v___y_1982_;
v___y_1933_ = v___y_1983_;
v_wf_1934_ = v_a_1994_;
v___y_1935_ = v___y_1985_;
v___y_1936_ = v___y_1986_;
v___y_1937_ = v___y_1987_;
v___y_1938_ = v___y_1988_;
v___y_1939_ = v___y_1989_;
v___y_1940_ = v___y_1990_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
v_a_1995_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
v___jp_2003_:
{
lean_object* v___x_2010_; lean_object* v_env_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_get(v___y_2009_);
v_env_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_ref(v_env_2011_);
lean_dec(v___x_2010_);
v___x_2012_ = l_Lean_Environment_unlockAsync(v_env_2011_);
v___x_2013_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_2012_, v___f_1978_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2032_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v_fst_2015_ = lean_ctor_get(v_a_2014_, 0);
v_snd_2016_ = lean_ctor_get(v_a_2014_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2018_ = v_a_2014_;
v_isShared_2019_ = v_isSharedCheck_2032_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v_a_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2032_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v_a_2021_; lean_object* v___f_2022_; uint8_t v___x_2023_; 
v___x_2020_ = l_Lean_Elab_wfRecursion___lam__1(v___x_1930_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
lean_inc(v_fst_1866_);
lean_inc(v_fst_1862_);
lean_inc(v_fst_2015_);
lean_inc(v_a_1836_);
v___f_2022_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2022_, 0, v_a_1836_);
lean_closure_set(v___f_2022_, 1, v_fst_2015_);
lean_closure_set(v___f_2022_, 2, v_fst_1862_);
lean_closure_set(v___f_2022_, 3, v_fst_1866_);
v___x_2023_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
if (v___x_2023_ == 0)
{
lean_del_object(v___x_2018_);
v___y_1982_ = v_fst_2015_;
v___y_1983_ = v_snd_2016_;
v___y_1984_ = v___f_2022_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2006_;
v___y_1988_ = v___y_2007_;
v___y_1989_ = v___y_2008_;
v___y_1990_ = v___y_2009_;
goto v___jp_1981_;
}
else
{
lean_object* v_value_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v_value_2024_ = lean_ctor_get(v_snd_1867_, 7);
v___x_2025_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2024_);
v___x_2026_ = l_Lean_MessageData_ofExpr(v_value_2024_);
v___x_2027_ = l_Lean_indentD(v___x_2026_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 7);
lean_ctor_set(v___x_2018_, 1, v___x_2027_);
lean_ctor_set(v___x_2018_, 0, v___x_2025_);
v___x_2029_ = v___x_2018_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1930_, v___x_2029_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec_ref_known(v___x_2030_, 1);
v___y_1982_ = v_fst_2015_;
v___y_1983_ = v_snd_2016_;
v___y_1984_ = v___f_2022_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2006_;
v___y_1988_ = v___y_2007_;
v___y_1989_ = v___y_2008_;
v___y_1990_ = v___y_2009_;
goto v___jp_1981_;
}
else
{
lean_dec_ref(v___f_2022_);
lean_dec(v_snd_2016_);
lean_dec(v_fst_2015_);
lean_dec(v_termMeasures_x3f_1980_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_termMeasures_x3f_1980_);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1836_);
lean_dec_ref(v_docCtx_1823_);
v_a_2033_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2013_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2013_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_1836_);
lean_dec_ref(v_termMeasure_x3fs_1825_);
lean_dec_ref(v_docCtx_1823_);
v_a_2050_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1859_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1859_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
v___jp_1841_:
{
size_t v_sz_1850_; lean_object* v___x_1851_; 
v_sz_1850_ = lean_array_size(v___y_1842_);
lean_inc(v___y_1843_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1843_, v___y_1842_, v_sz_1850_, v___x_1834_, v___x_1840_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; 
lean_dec_ref_known(v___x_1851_, 1);
v___x_1852_ = l_Lean_enableRealizationsForConst(v___y_1843_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1852_, 1);
v___x_1853_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1842_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1853_;
}
else
{
lean_dec_ref(v___y_1842_);
return v___x_1852_;
}
}
else
{
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_termMeasure_x3fs_1825_);
lean_dec_ref(v_docCtx_1823_);
v_a_2058_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1835_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1835_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2066_, lean_object* v_preDefs_2067_, lean_object* v_termMeasure_x3fs_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Elab_wfRecursion(v_docCtx_2066_, v_preDefs_2067_, v_termMeasure_x3fs_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2077_, lean_object* v_msg_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2087_, v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2097_, size_t v_i_2098_, lean_object* v_bs_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2097_, v_i_2098_, v_bs_2099_, v___y_2104_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_bs_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2118_, v_i_boxed_2119_, v_bs_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2121_, v_sz_2122_, v_i_2123_, v_b_2124_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2133_, lean_object* v_sz_2134_, lean_object* v_i_2135_, lean_object* v_b_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2134_);
lean_dec(v_sz_2134_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2133_, v_sz_boxed_2144_, v_i_boxed_2145_, v_b_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec_ref(v_as_2133_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2147_, lean_object* v_as_2148_, size_t v_sz_2149_, size_t v_i_2150_, lean_object* v_bs_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2147_, v_sz_2149_, v_i_2150_, v_bs_2151_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2160_, lean_object* v_as_2161_, lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_bs_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
size_t v_sz_boxed_2172_; size_t v_i_boxed_2173_; lean_object* v_res_2174_; 
v_sz_boxed_2172_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2173_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2160_, v_as_2161_, v_sz_boxed_2172_, v_i_boxed_2173_, v_bs_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_as_2161_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2175_, lean_object* v___x_2176_, size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2175_, v___x_2176_, v_sz_2177_, v_i_2178_, v_bs_2179_, v___y_2184_, v___y_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2188_, lean_object* v___x_2189_, lean_object* v_sz_2190_, lean_object* v_i_2191_, lean_object* v_bs_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2190_);
lean_dec(v_sz_2190_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2188_, v___x_2189_, v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2203_, lean_object* v_env_2204_, lean_object* v_x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2204_, v_x_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_env_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2214_, v_env_2215_, v_x_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2225_, lean_object* v_msg_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2225_, v_msg_2226_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2235_, lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2235_, v_msg_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_bs_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2245_, v_i_2246_, v_bs_2247_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_bs_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2266_, v_i_boxed_2267_, v_bs_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2269_, lean_object* v_as_2270_, size_t v_sz_2271_, size_t v_i_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2269_, v_as_2270_, v_sz_2271_, v_i_2272_, v_b_2273_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2282_, lean_object* v_as_2283_, lean_object* v_sz_2284_, lean_object* v_i_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
size_t v_sz_boxed_2294_; size_t v_i_boxed_2295_; lean_object* v_res_2296_; 
v_sz_boxed_2294_ = lean_unbox_usize(v_sz_2284_);
lean_dec(v_sz_2284_);
v_i_boxed_2295_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2282_, v_as_2283_, v_sz_boxed_2294_, v_i_boxed_2295_, v_b_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_as_2283_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2297_, lean_object* v_x_2298_, uint8_t v_isExporting_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2298_, v_isExporting_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_x_2309_, lean_object* v_isExporting_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v_isExporting_boxed_2318_; lean_object* v_res_2319_; 
v_isExporting_boxed_2318_ = lean_unbox(v_isExporting_2310_);
v_res_2319_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2308_, v_x_2309_, v_isExporting_boxed_2318_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2320_, lean_object* v_x_2321_, uint8_t v_when_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2321_, v_when_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2331_, lean_object* v_x_2332_, lean_object* v_when_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_when_boxed_2341_; lean_object* v_res_2342_; 
v_when_boxed_2341_ = lean_unbox(v_when_2333_);
v_res_2342_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2331_, v_x_2332_, v_when_boxed_2341_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2343_, lean_object* v_macroStack_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2343_, v_macroStack_2344_, v___y_2349_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2353_, lean_object* v_macroStack_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2353_, v_macroStack_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2363_, lean_object* v_msgData_2364_, uint8_t v_severity_2365_, uint8_t v_isSilent_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2363_, v_msgData_2364_, v_severity_2365_, v_isSilent_2366_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2375_, lean_object* v_msgData_2376_, lean_object* v_severity_2377_, lean_object* v_isSilent_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_severity_boxed_2386_; uint8_t v_isSilent_boxed_2387_; lean_object* v_res_2388_; 
v_severity_boxed_2386_ = lean_unbox(v_severity_2377_);
v_isSilent_boxed_2387_ = lean_unbox(v_isSilent_2378_);
v_res_2388_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2375_, v_msgData_2376_, v_severity_boxed_2386_, v_isSilent_boxed_2387_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_ref_2375_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2460_ = 0;
v___x_2461_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2462_ = l_Lean_registerTraceClass(v___x_2459_, v___x_2460_, v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2464_;
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
