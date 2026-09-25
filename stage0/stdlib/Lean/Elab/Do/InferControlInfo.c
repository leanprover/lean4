// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term public import Lean.Elab.Do.ForwardSyntax meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = ", numRegularExits: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ",\n    noFallthrough: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value)} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 75, 74, 17, 172, 74, 138, 206)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 182, 102, 169, 76, 87, 55, 254)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 65, 144, 138, 55, 55, 217, 220)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ControlInfoHandler"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 126, 127, 228, 104, 205, 61, 148)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "control info inference"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 238, .m_capacity = 238, .m_length = 235, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`."};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(119) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(127) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not a let or reassignment declaration: "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Not a catch or catch match: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doErasedArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value),LEAN_SCALAR_PTR_LITERAL(176, 216, 203, 158, 108, 103, 134, 112)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doErased"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value),LEAN_SCALAR_PTR_LITERAL(69, 69, 120, 16, 133, 86, 56, 26)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = 0;
v___x_4_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4_, 0, v___x_2_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 1, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 3, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0(void){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_8_ = l_Lean_NameSet_empty;
v___x_9_ = 1;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = 0;
v___x_12_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_8_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 1, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 3, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_empty___closed__0, &l_Lean_Elab_Do_ControlInfo_empty___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v_breaks_16_; uint8_t v_continues_17_; uint8_t v_returnsEarly_18_; uint8_t v_noFallthrough_19_; lean_object* v_reassigns_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_52_; 
v_breaks_16_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2);
v_continues_17_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 1);
v_returnsEarly_18_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 2);
v_noFallthrough_19_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 3);
v_reassigns_20_ = lean_ctor_get(v_a_14_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_a_14_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v_a_14_, 0);
lean_dec(v_unused_53_);
v___x_22_ = v_a_14_;
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_reassigns_20_);
lean_dec(v_a_14_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; uint8_t v___y_28_; lean_object* v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
if (v_breaks_16_ == 0)
{
uint8_t v_breaks_51_; 
v_breaks_51_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2);
v___y_49_ = v_breaks_51_;
goto v___jp_48_;
}
else
{
v___y_49_ = v_breaks_16_;
goto v___jp_48_;
}
v___jp_24_:
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_29_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_26_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_26_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_27_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_28_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 3, v___y_30_);
return v___x_33_;
}
}
v___jp_35_:
{
if (v_noFallthrough_19_ == 0)
{
lean_object* v_numRegularExits_39_; uint8_t v_noFallthrough_40_; lean_object* v_reassigns_41_; 
v_numRegularExits_39_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_39_);
v_noFallthrough_40_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 3);
v_reassigns_41_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_41_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v_numRegularExits_39_;
v___y_27_ = v___y_36_;
v___y_28_ = v___y_37_;
v___y_29_ = v_reassigns_41_;
v___y_30_ = v_noFallthrough_40_;
goto v___jp_24_;
}
else
{
lean_object* v_numRegularExits_42_; lean_object* v_reassigns_43_; 
v_numRegularExits_42_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_42_);
v_reassigns_43_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_43_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v_numRegularExits_42_;
v___y_27_ = v___y_36_;
v___y_28_ = v___y_37_;
v___y_29_ = v_reassigns_43_;
v___y_30_ = v_noFallthrough_19_;
goto v___jp_24_;
}
}
v___jp_44_:
{
if (v_returnsEarly_18_ == 0)
{
uint8_t v_returnsEarly_47_; 
v_returnsEarly_47_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 2);
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
v___y_38_ = v_returnsEarly_18_;
goto v___jp_35_;
}
}
v___jp_48_:
{
if (v_continues_17_ == 0)
{
uint8_t v_continues_50_; 
v_continues_50_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 1);
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_50_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_17_;
goto v___jp_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; uint8_t v___y_60_; uint8_t v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
v_breaks_66_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2);
v_continues_67_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 1);
v_returnsEarly_68_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 2);
v_numRegularExits_69_ = lean_ctor_get(v_a_54_, 0);
lean_inc(v_numRegularExits_69_);
v_noFallthrough_70_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 3);
v_reassigns_71_ = lean_ctor_get(v_a_54_, 1);
lean_inc(v_reassigns_71_);
lean_dec_ref(v_a_54_);
if (v_breaks_66_ == 0)
{
uint8_t v_breaks_87_; 
v_breaks_87_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2);
v___y_85_ = v_breaks_87_;
goto v___jp_84_;
}
else
{
v___y_85_ = v_breaks_66_;
goto v___jp_84_;
}
v___jp_56_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_NameSet_append(v___y_59_, v___y_58_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_62_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_61_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_60_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_57_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 3, v___y_63_);
return v___x_65_;
}
v___jp_72_:
{
lean_object* v_numRegularExits_76_; uint8_t v_noFallthrough_77_; lean_object* v_reassigns_78_; lean_object* v___x_79_; 
v_numRegularExits_76_ = lean_ctor_get(v_b_55_, 0);
lean_inc(v_numRegularExits_76_);
v_noFallthrough_77_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 3);
v_reassigns_78_ = lean_ctor_get(v_b_55_, 1);
lean_inc(v_reassigns_78_);
lean_dec_ref(v_b_55_);
v___x_79_ = lean_nat_add(v_numRegularExits_69_, v_numRegularExits_76_);
lean_dec(v_numRegularExits_76_);
lean_dec(v_numRegularExits_69_);
if (v_noFallthrough_70_ == 0)
{
v___y_57_ = v___y_75_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v___y_73_;
v___y_61_ = v___y_74_;
v___y_62_ = v___x_79_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_75_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v___y_73_;
v___y_61_ = v___y_74_;
v___y_62_ = v___x_79_;
v___y_63_ = v_noFallthrough_77_;
goto v___jp_56_;
}
}
v___jp_80_:
{
if (v_returnsEarly_68_ == 0)
{
uint8_t v_returnsEarly_83_; 
v_returnsEarly_83_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 2);
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_83_;
goto v___jp_72_;
}
else
{
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_68_;
goto v___jp_72_;
}
}
v___jp_84_:
{
if (v_continues_67_ == 0)
{
uint8_t v_continues_86_; 
v_continues_86_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 1);
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_86_;
goto v___jp_80_;
}
else
{
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_67_;
goto v___jp_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_88_, lean_object* v_x2_89_, lean_object* v_x3_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x1_88_);
lean_ctor_set(v___x_91_, 1, v_x3_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_94_ = l_Lean_stringToMessageData(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_117_ = l_Lean_stringToMessageData(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_120_ = l_Lean_stringToMessageData(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_132_, lean_object* v_info_133_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; uint8_t v_breaks_150_; uint8_t v_continues_151_; uint8_t v_returnsEarly_152_; lean_object* v_numRegularExits_153_; uint8_t v_noFallthrough_154_; lean_object* v_reassigns_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___x_182_; lean_object* v___y_184_; 
v_breaks_150_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2);
v_continues_151_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 1);
v_returnsEarly_152_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 2);
v_numRegularExits_153_ = lean_ctor_get(v_info_133_, 0);
lean_inc(v_numRegularExits_153_);
v_noFallthrough_154_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 3);
v_reassigns_155_ = lean_ctor_get(v_info_133_, 1);
lean_inc(v_reassigns_155_);
lean_dec_ref(v_info_133_);
v___x_182_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
if (v_breaks_150_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_184_ = v___x_193_;
goto v___jp_183_;
}
v___jp_134_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc_ref(v___y_137_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___y_137_);
v___x_139_ = l_Lean_MessageData_ofFormat(v___x_138_);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_136_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_box(0);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11));
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_144_, v___f_132_, v___x_143_, v___y_135_);
v___x_146_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12));
v___x_147_ = l_List_mapTR_loop___redArg(v___x_146_, v___x_145_, v___x_143_);
v___x_148_ = l_Lean_MessageData_ofList(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_142_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
v___jp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v___y_158_);
v___x_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_159_, 0, v___y_158_);
v___x_160_ = l_Lean_MessageData_ofFormat(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Nat_reprFast(v_numRegularExits_153_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
if (v_noFallthrough_154_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_170_;
goto v___jp_134_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_171_;
goto v___jp_134_;
}
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref(v___y_174_);
v___x_175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_175_, 0, v___y_174_);
v___x_176_ = l_Lean_MessageData_ofFormat(v___x_175_);
v___x_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_173_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_returnsEarly_152_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_180_;
goto v___jp_156_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_181_;
goto v___jp_156_;
}
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc_ref(v___y_184_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___y_184_);
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_182_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
if (v_continues_151_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_190_;
goto v___jp_172_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_191_;
goto v___jp_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_225_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_226_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_227_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_228_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_229_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_228_, v_ref_222_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_241_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_248_ = l_Lean_addBuiltinDocString(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_279_ = l_Lean_addBuiltinDeclarationRanges(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_toCold_291_; lean_object* v_mctx_292_; lean_object* v_lctx_293_; lean_object* v_options_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_toCold_291_ = lean_ctor_get(v___y_285_, 0);
v_mctx_292_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_292_);
lean_dec(v___x_290_);
v_lctx_293_ = lean_ctor_get(v___y_283_, 2);
v_options_294_ = lean_ctor_get(v_toCold_291_, 2);
lean_inc_ref(v_options_294_);
lean_inc_ref(v_lctx_293_);
v___x_295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_295_, 0, v_env_289_);
lean_ctor_set(v___x_295_, 1, v_mctx_292_);
lean_ctor_set(v___x_295_, 2, v_lctx_293_);
lean_ctor_set(v___x_295_, 3, v_options_294_);
v___x_296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_msgData_282_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(1);
v___x_306_ = l_Lean_MessageData_ofFormat(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
return v_x_312_;
}
else
{
lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_337_; 
v_head_314_ = lean_ctor_get(v_x_313_, 0);
v_tail_315_ = lean_ctor_get(v_x_313_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_337_ == 0)
{
v___x_317_ = v_x_313_;
v_isShared_318_ = v_isSharedCheck_337_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_head_314_);
lean_dec(v_x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_337_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_before_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_335_; 
v_before_319_ = lean_ctor_get(v_head_314_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_head_314_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_head_314_, 1);
lean_dec(v_unused_336_);
v___x_321_ = v_head_314_;
v_isShared_322_ = v_isSharedCheck_335_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_before_319_);
lean_dec(v_head_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_335_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 7);
lean_ctor_set(v___x_321_, 1, v___x_323_);
lean_ctor_set(v___x_321_, 0, v_x_312_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_x_312_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_334_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 7);
lean_ctor_set(v___x_317_, 1, v___x_326_);
lean_ctor_set(v___x_317_, 0, v___x_325_);
v___x_328_ = v___x_317_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_333_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_MessageData_ofSyntax(v_before_319_);
v___x_330_ = l_Lean_indentD(v___x_329_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_x_312_ = v___x_331_;
v_x_313_ = v_tail_315_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_338_, lean_object* v_opt_339_){
_start:
{
lean_object* v_name_340_; lean_object* v_defValue_341_; lean_object* v_map_342_; lean_object* v___x_343_; 
v_name_340_ = lean_ctor_get(v_opt_339_, 0);
v_defValue_341_ = lean_ctor_get(v_opt_339_, 1);
v_map_342_ = lean_ctor_get(v_opts_338_, 0);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_342_, v_name_340_);
if (lean_obj_tag(v___x_343_) == 0)
{
uint8_t v___x_344_; 
v___x_344_ = lean_unbox(v_defValue_341_);
return v___x_344_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_343_, 1);
if (lean_obj_tag(v_val_345_) == 1)
{
uint8_t v_v_346_; 
v_v_346_ = lean_ctor_get_uint8(v_val_345_, 0);
lean_dec_ref_known(v_val_345_, 0);
return v_v_346_;
}
else
{
uint8_t v___x_347_; 
lean_dec(v_val_345_);
v___x_347_ = lean_unbox(v_defValue_341_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_348_, lean_object* v_opt_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_348_, v_opt_349_);
lean_dec_ref(v_opt_349_);
lean_dec_ref(v_opts_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_356_ = l_Lean_MessageData_ofFormat(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_357_, lean_object* v_macroStack_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_359_);
v___x_362_ = l_Lean_Elab_pp_macroStack;
v___x_363_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v___x_361_, v___x_362_);
lean_dec_ref(v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec(v_macroStack_358_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_msgData_357_);
return v___x_364_;
}
else
{
if (lean_obj_tag(v_macroStack_358_) == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_msgData_357_);
return v___x_365_;
}
else
{
lean_object* v_head_366_; lean_object* v_after_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_382_; 
v_head_366_ = lean_ctor_get(v_macroStack_358_, 0);
lean_inc(v_head_366_);
v_after_367_ = lean_ctor_get(v_head_366_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_head_366_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_head_366_, 0);
lean_dec(v_unused_383_);
v___x_369_ = v_head_366_;
v_isShared_370_ = v_isSharedCheck_382_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_after_367_);
lean_dec(v_head_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_382_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 7);
lean_ctor_set(v___x_369_, 1, v___x_371_);
lean_ctor_set(v___x_369_, 0, v_msgData_357_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_msgData_357_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_381_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_msgData_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_374_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_MessageData_ofSyntax(v_after_367_);
v___x_377_ = l_Lean_indentD(v___x_376_);
v_msgData_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_378_, 0, v___x_375_);
lean_ctor_set(v_msgData_378_, 1, v___x_377_);
v___x_379_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_378_, v_macroStack_358_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_384_, lean_object* v_macroStack_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_384_, v_macroStack_385_, v___y_386_);
lean_dec_ref(v___y_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_ref_397_; lean_object* v_macroStack_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_ref_397_ = lean_ctor_get(v___y_394_, 2);
v_macroStack_398_ = lean_ctor_get(v___y_390_, 1);
v___x_399_ = l_Lean_Elab_getBetterRef(v_ref_397_, v_macroStack_398_);
v___x_400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_389_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
lean_inc(v_macroStack_398_);
v___x_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_401_, v_macroStack_398_, v___y_394_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_399_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_421_, size_t v_i_422_, size_t v_stop_423_, lean_object* v_b_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_eq(v_i_422_, v_stop_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; 
v___x_426_ = lean_array_uget_borrowed(v_as_421_, v_i_422_);
lean_inc(v___x_426_);
v___x_427_ = l_Lean_NameSet_insert(v_b_424_, v___x_426_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_422_, v___x_428_);
v_i_422_ = v___x_429_;
v_b_424_ = v___x_427_;
goto _start;
}
else
{
return v_b_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_){
_start:
{
size_t v_i_boxed_435_; size_t v_stop_boxed_436_; lean_object* v_res_437_; 
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_436_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_431_, v_i_boxed_435_, v_stop_boxed_436_, v_b_434_);
lean_dec_ref(v_as_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_438_, size_t v_i_439_, lean_object* v_bs_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_441_ == 0)
{
return v_bs_440_;
}
else
{
lean_object* v_v_442_; lean_object* v___x_443_; lean_object* v_bs_x27_444_; lean_object* v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v_v_442_ = lean_array_uget(v_bs_440_, v_i_439_);
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_440_, v_i_439_, v___x_443_);
v___x_445_ = l_Lean_TSyntax_getId(v_v_442_);
lean_dec(v_v_442_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_439_, v___x_446_);
v___x_448_ = lean_array_uset(v_bs_x27_444_, v_i_439_, v___x_445_);
v_i_439_ = v___x_447_;
v_bs_440_ = v___x_448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_bs_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_454_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_453_, v_i_boxed_454_, v_bs_452_);
return v_res_455_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_464_, size_t v_i_465_, lean_object* v_bs_466_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_465_, v_sz_464_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_bs_466_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v_bs_x27_470_; lean_object* v___x_471_; size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v_bs_x27_470_ = lean_array_uset(v_bs_466_, v_i_465_, v___x_469_);
v___x_471_ = lean_box(0);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_add(v_i_465_, v___x_472_);
v___x_474_ = lean_array_uset(v_bs_x27_470_, v_i_465_, v___x_471_);
v_i_465_ = v___x_473_;
v_bs_466_ = v___x_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_bs_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_480_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_479_, v_i_boxed_480_, v_bs_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_482_, uint8_t v___x_483_, lean_object* v_as_484_, size_t v_i_485_, size_t v_stop_486_, lean_object* v_b_487_){
_start:
{
lean_object* v___y_489_; uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_eq(v_i_485_, v_stop_486_);
if (v___x_493_ == 0)
{
lean_object* v_fst_494_; uint8_t v___x_495_; 
v_fst_494_ = lean_ctor_get(v_b_487_, 0);
v___x_495_ = lean_unbox(v_fst_494_);
if (v___x_495_ == 0)
{
lean_object* v_snd_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_snd_496_ = lean_ctor_get(v_b_487_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_b_487_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_b_487_, 0);
lean_dec(v_unused_505_);
v___x_498_ = v_b_487_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snd_496_);
lean_dec(v_b_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_box(v___x_482_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_496_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v___y_489_ = v___x_502_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_snd_506_ = lean_ctor_get(v_b_487_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_b_487_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_b_487_, 0);
lean_dec(v_unused_517_);
v___x_508_ = v_b_487_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_dec(v_b_487_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_510_ = lean_array_uget_borrowed(v_as_484_, v_i_485_);
lean_inc(v___x_510_);
v___x_511_ = lean_array_push(v_snd_506_, v___x_510_);
v___x_512_ = lean_box(v___x_483_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_511_);
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_511_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v___y_489_ = v___x_514_;
goto v___jp_488_;
}
}
}
}
else
{
return v_b_487_;
}
v___jp_488_:
{
size_t v___x_490_; size_t v___x_491_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_485_, v___x_490_);
v_i_485_ = v___x_491_;
v_b_487_ = v___y_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_, lean_object* v_b_523_){
_start:
{
uint8_t v___x_175738__boxed_524_; uint8_t v___x_175739__boxed_525_; size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v___x_175738__boxed_524_ = lean_unbox(v___x_518_);
v___x_175739__boxed_525_ = lean_unbox(v___x_519_);
v_i_boxed_526_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_175738__boxed_524_, v___x_175739__boxed_525_, v_as_520_, v_i_boxed_526_, v_stop_boxed_527_, v_b_523_);
lean_dec_ref(v_as_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_529_, lean_object* v___y_530_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_a_531_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v_a_531_);
lean_ctor_set(v___x_532_, 1, v___y_530_);
return v___x_532_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_a_533_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_533_);
lean_ctor_set(v___x_534_, 1, v___y_530_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_535_, v___y_536_);
lean_dec_ref(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_538_, lean_object* v_stx_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_538_, v_stx_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
if (lean_obj_tag(v_a_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_a_544_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_553_);
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_box(0);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_a_544_);
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
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_582_; 
v_val_554_ = lean_ctor_get(v_a_543_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_582_ == 0)
{
v___x_556_ = v_a_543_;
v_isShared_557_ = v_isSharedCheck_582_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v_a_543_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_582_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_snd_558_; 
v_snd_558_ = lean_ctor_get(v_val_554_, 1);
lean_inc(v_snd_558_);
lean_dec(v_val_554_);
if (lean_obj_tag(v_snd_558_) == 0)
{
lean_object* v_a_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_556_);
v_a_559_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_542_, 2);
v_a_560_ = lean_ctor_get(v_snd_558_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_snd_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v_snd_558_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v_snd_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_565_, v_a_559_);
lean_dec_ref(v___x_565_);
return v___x_566_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_581_; 
v_a_569_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_542_, 2);
v_a_570_ = lean_ctor_get(v_snd_558_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_snd_558_);
if (v_isSharedCheck_581_ == 0)
{
v___x_572_ = v_snd_558_;
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_snd_558_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_a_570_);
v___x_575_ = v___x_556_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_580_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_575_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_577_, v_a_569_);
lean_dec_ref(v___x_577_);
return v___x_578_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_583_ = lean_ctor_get(v___x_542_, 0);
v_a_584_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_542_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_inc(v_a_583_);
lean_dec(v___x_542_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_592_, lean_object* v_stx_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_592_, v_stx_593_, v___y_594_, v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = l_Lean_maxRecDepthErrorMessage;
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_605_ = l_Lean_MessageData_ofFormat(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_607_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_ref_609_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_617_, lean_object* v_declName_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___x_621_; lean_object* v_env_622_; lean_object* v___x_623_; uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_621_ = 0;
v_env_622_ = l_Lean_Environment_setExporting(v_env_617_, v___x_621_);
lean_inc(v_declName_618_);
v___x_623_ = l_Lean_mkPrivateName(v_env_622_, v_declName_618_);
v___x_624_ = 1;
lean_inc_ref(v_env_622_);
v___x_625_ = l_Lean_Environment_contains(v_env_622_, v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = l_Lean_privateToUserName(v_declName_618_);
v___x_627_ = l_Lean_Environment_contains(v_env_622_, v___x_626_, v___x_624_);
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___y_620_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_env_622_);
lean_dec(v_declName_618_);
v___x_630_ = lean_box(v___x_625_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_620_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_632_, lean_object* v_declName_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_632_, v_declName_633_, v___y_634_, v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_637_, lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_toCold_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; uint16_t v_optionFlags_649_; uint8_t v_suppressElabErrors_650_; uint8_t v_isRecordingDeps_651_; lean_object* v_ref_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_toCold_646_ = lean_ctor_get(v___y_643_, 0);
v_currRecDepth_647_ = lean_ctor_get(v___y_643_, 1);
v_ref_648_ = lean_ctor_get(v___y_643_, 2);
v_optionFlags_649_ = lean_ctor_get_uint16(v___y_643_, sizeof(void*)*3);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*3 + 2);
v_isRecordingDeps_651_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*3 + 3);
v_ref_652_ = l_Lean_replaceRef(v_ref_637_, v_ref_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_toCold_646_);
v___x_653_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_653_, 0, v_toCold_646_);
lean_ctor_set(v___x_653_, 1, v_currRecDepth_647_);
lean_ctor_set(v___x_653_, 2, v_ref_652_);
lean_ctor_set_uint16(v___x_653_, sizeof(void*)*3, v_optionFlags_649_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 2, v_suppressElabErrors_650_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 3, v_isRecordingDeps_651_);
v___x_654_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___x_653_, v___y_644_);
lean_dec_ref_known(v___x_653_, 3);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_655_, v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_ref_655_);
return v_res_664_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_665_; double v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_float_of_nat(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_670_, lean_object* v_msg_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_724_; 
v_ref_677_ = lean_ctor_get(v___y_674_, 2);
v___x_678_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_724_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_724_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_724_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_traceState_684_; lean_object* v_env_685_; lean_object* v_nextMacroScope_686_; lean_object* v_ngen_687_; lean_object* v_auxDeclNGen_688_; lean_object* v_cache_689_; lean_object* v_recordedDeps_690_; lean_object* v_messages_691_; lean_object* v_infoState_692_; lean_object* v_snapshotTasks_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_723_; 
v___x_683_ = lean_st_ref_take(v___y_675_);
v_traceState_684_ = lean_ctor_get(v___x_683_, 4);
v_env_685_ = lean_ctor_get(v___x_683_, 0);
v_nextMacroScope_686_ = lean_ctor_get(v___x_683_, 1);
v_ngen_687_ = lean_ctor_get(v___x_683_, 2);
v_auxDeclNGen_688_ = lean_ctor_get(v___x_683_, 3);
v_cache_689_ = lean_ctor_get(v___x_683_, 5);
v_recordedDeps_690_ = lean_ctor_get(v___x_683_, 6);
v_messages_691_ = lean_ctor_get(v___x_683_, 7);
v_infoState_692_ = lean_ctor_get(v___x_683_, 8);
v_snapshotTasks_693_ = lean_ctor_get(v___x_683_, 9);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_723_ == 0)
{
v___x_695_ = v___x_683_;
v_isShared_696_ = v_isSharedCheck_723_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snapshotTasks_693_);
lean_inc(v_infoState_692_);
lean_inc(v_messages_691_);
lean_inc(v_recordedDeps_690_);
lean_inc(v_cache_689_);
lean_inc(v_traceState_684_);
lean_inc(v_auxDeclNGen_688_);
lean_inc(v_ngen_687_);
lean_inc(v_nextMacroScope_686_);
lean_inc(v_env_685_);
lean_dec(v___x_683_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_723_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint64_t v_tid_697_; lean_object* v_traces_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_722_; 
v_tid_697_ = lean_ctor_get_uint64(v_traceState_684_, sizeof(void*)*1);
v_traces_698_ = lean_ctor_get(v_traceState_684_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_traceState_684_);
if (v_isSharedCheck_722_ == 0)
{
v___x_700_ = v_traceState_684_;
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_traces_698_);
lean_dec(v_traceState_684_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; double v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_box(0);
v___x_704_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_705_ = 0;
v___x_706_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_707_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_707_, 0, v_cls_670_);
lean_ctor_set(v___x_707_, 1, v___x_703_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
lean_ctor_set_float(v___x_707_, sizeof(void*)*3, v___x_704_);
lean_ctor_set_float(v___x_707_, sizeof(void*)*3 + 8, v___x_704_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*3 + 16, v___x_705_);
v___x_708_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_709_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v_a_679_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
lean_inc(v_ref_677_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_ref_677_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_PersistentArray_push___redArg(v_traces_698_, v___x_710_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_711_);
v___x_713_ = v___x_700_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_711_);
lean_ctor_set_uint64(v_reuseFailAlloc_721_, sizeof(void*)*1, v_tid_697_);
v___x_713_ = v_reuseFailAlloc_721_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 4, v___x_713_);
v___x_715_ = v___x_695_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_env_685_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_nextMacroScope_686_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_ngen_687_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_auxDeclNGen_688_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_720_, 5, v_cache_689_);
lean_ctor_set(v_reuseFailAlloc_720_, 6, v_recordedDeps_690_);
lean_ctor_set(v_reuseFailAlloc_720_, 7, v_messages_691_);
lean_ctor_set(v_reuseFailAlloc_720_, 8, v_infoState_692_);
lean_ctor_set(v_reuseFailAlloc_720_, 9, v_snapshotTasks_693_);
v___x_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_st_ref_put(v___y_675_, v___x_715_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_702_);
v___x_718_ = v___x_681_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_702_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_725_, v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
if (lean_obj_tag(v_as_736_) == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_box(0);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
else
{
lean_object* v_toCold_746_; lean_object* v_options_747_; uint8_t v_hasTrace_748_; 
v_toCold_746_ = lean_ctor_get(v___y_741_, 0);
v_options_747_ = lean_ctor_get(v_toCold_746_, 2);
v_hasTrace_748_ = lean_ctor_get_uint8(v_options_747_, sizeof(void*)*1);
if (v_hasTrace_748_ == 0)
{
lean_object* v_tail_749_; 
v_tail_749_ = lean_ctor_get(v_as_736_, 1);
lean_inc(v_tail_749_);
lean_dec_ref_known(v_as_736_, 2);
v_as_736_ = v_tail_749_;
goto _start;
}
else
{
lean_object* v_head_751_; lean_object* v_tail_752_; lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v_inheritedTraceOptions_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_head_751_ = lean_ctor_get(v_as_736_, 0);
lean_inc(v_head_751_);
v_tail_752_ = lean_ctor_get(v_as_736_, 1);
lean_inc(v_tail_752_);
lean_dec_ref_known(v_as_736_, 2);
v_fst_753_ = lean_ctor_get(v_head_751_, 0);
lean_inc_n(v_fst_753_, 2);
v_snd_754_ = lean_ctor_get(v_head_751_, 1);
lean_inc(v_snd_754_);
lean_dec(v_head_751_);
v_inheritedTraceOptions_755_ = lean_ctor_get(v_toCold_746_, 11);
v___x_756_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_757_ = l_Lean_Name_append(v___x_756_, v_fst_753_);
v___x_758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_755_, v_options_747_, v___x_757_);
lean_dec(v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_snd_754_);
lean_dec(v_fst_753_);
v_as_736_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v_snd_754_);
v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
v___x_762_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_753_, v___x_761_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref_known(v___x_762_, 1);
v_as_736_ = v_tail_752_;
goto _start;
}
else
{
lean_dec(v_tail_752_);
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(0);
return v___x_775_;
}
else
{
lean_object* v_key_776_; lean_object* v_value_777_; lean_object* v_tail_778_; uint8_t v___x_779_; 
v_key_776_ = lean_ctor_get(v_x_774_, 0);
v_value_777_ = lean_ctor_get(v_x_774_, 1);
v_tail_778_ = lean_ctor_get(v_x_774_, 2);
v___x_779_ = lean_name_eq(v_key_776_, v_a_773_);
if (v___x_779_ == 0)
{
v_x_774_ = v_tail_778_;
goto _start;
}
else
{
lean_object* v___x_781_; 
lean_inc(v_value_777_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_value_777_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_782_, lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_782_, v_x_783_);
lean_dec(v_x_783_);
lean_dec(v_a_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_buckets_787_; lean_object* v___x_788_; uint64_t v___y_790_; 
v_buckets_787_ = lean_ctor_get(v_m_785_, 1);
v___x_788_ = lean_array_get_size(v_buckets_787_);
if (lean_obj_tag(v_a_786_) == 0)
{
uint64_t v___x_804_; 
v___x_804_ = 1723ULL;
v___y_790_ = v___x_804_;
goto v___jp_789_;
}
else
{
uint64_t v_hash_805_; 
v_hash_805_ = lean_ctor_get_uint64(v_a_786_, sizeof(void*)*2);
v___y_790_ = v_hash_805_;
goto v___jp_789_;
}
v___jp_789_:
{
uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v_fold_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_791_ = 32ULL;
v___x_792_ = lean_uint64_shift_right(v___y_790_, v___x_791_);
v_fold_793_ = lean_uint64_xor(v___y_790_, v___x_792_);
v___x_794_ = 16ULL;
v___x_795_ = lean_uint64_shift_right(v_fold_793_, v___x_794_);
v___x_796_ = lean_uint64_xor(v_fold_793_, v___x_795_);
v___x_797_ = lean_uint64_to_usize(v___x_796_);
v___x_798_ = lean_usize_of_nat(v___x_788_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_sub(v___x_798_, v___x_799_);
v___x_801_ = lean_usize_land(v___x_797_, v___x_800_);
v___x_802_ = lean_array_uget_borrowed(v_buckets_787_, v___x_801_);
v___x_803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_786_, v___x_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_m_806_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_809_, lean_object* v_i_810_, lean_object* v_k_811_){
_start:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_array_get_size(v_keys_809_);
v___x_813_ = lean_nat_dec_lt(v_i_810_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_i_810_);
return v___x_813_;
}
else
{
lean_object* v_k_x27_814_; uint8_t v___x_815_; 
v_k_x27_814_ = lean_array_fget_borrowed(v_keys_809_, v_i_810_);
v___x_815_ = l_Lean_instBEqExtraModUse_beq(v_k_811_, v_k_x27_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_i_810_, v___x_816_);
lean_dec(v_i_810_);
v_i_810_ = v___x_817_;
goto _start;
}
else
{
lean_dec(v_i_810_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_819_, lean_object* v_i_820_, lean_object* v_k_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_819_, v_i_820_, v_k_821_);
lean_dec_ref(v_k_821_);
lean_dec_ref(v_keys_819_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_824_, size_t v_x_825_, lean_object* v_x_826_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v_es_827_; lean_object* v___x_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v_j_831_; lean_object* v___x_832_; 
v_es_827_ = lean_ctor_get(v_x_824_, 0);
v___x_828_ = lean_box(2);
v___x_829_ = ((size_t)31ULL);
v___x_830_ = lean_usize_land(v_x_825_, v___x_829_);
v_j_831_ = lean_usize_to_nat(v___x_830_);
v___x_832_ = lean_array_get_borrowed(v___x_828_, v_es_827_, v_j_831_);
lean_dec(v_j_831_);
switch(lean_obj_tag(v___x_832_))
{
case 0:
{
lean_object* v_key_833_; uint8_t v___x_834_; 
v_key_833_ = lean_ctor_get(v___x_832_, 0);
v___x_834_ = l_Lean_instBEqExtraModUse_beq(v_x_826_, v_key_833_);
return v___x_834_;
}
case 1:
{
lean_object* v_node_835_; size_t v___x_836_; size_t v___x_837_; 
v_node_835_ = lean_ctor_get(v___x_832_, 0);
v___x_836_ = ((size_t)5ULL);
v___x_837_ = lean_usize_shift_right(v_x_825_, v___x_836_);
v_x_824_ = v_node_835_;
v_x_825_ = v___x_837_;
goto _start;
}
default: 
{
uint8_t v___x_839_; 
v___x_839_ = 0;
return v___x_839_;
}
}
}
else
{
lean_object* v_ks_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_ks_840_ = lean_ctor_get(v_x_824_, 0);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_840_, v___x_841_, v_x_826_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
size_t v_x_176250__boxed_846_; uint8_t v_res_847_; lean_object* v_r_848_; 
v_x_176250__boxed_846_ = lean_unbox_usize(v_x_844_);
lean_dec(v_x_844_);
v_res_847_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_843_, v_x_176250__boxed_846_, v_x_845_);
lean_dec_ref(v_x_845_);
lean_dec_ref(v_x_843_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
uint64_t v___x_851_; size_t v___x_852_; uint8_t v___x_853_; 
v___x_851_ = l_Lean_instHashableExtraModUse_hash(v_x_850_);
v___x_852_ = lean_uint64_to_usize(v___x_851_);
v___x_853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_849_, v___x_852_, v_x_850_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_854_, v_x_855_);
lean_dec_ref(v_x_855_);
lean_dec_ref(v_x_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_858_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_865_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
lean_ctor_set(v___x_865_, 3, v___x_864_);
lean_ctor_set(v___x_865_, 4, v___x_864_);
lean_ctor_set(v___x_865_, 5, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_cls_877_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_878_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_879_ = l_Lean_Name_append(v___x_878_, v_cls_877_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_890_, uint8_t v_isMeta_891_, lean_object* v_hint_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_env_902_; uint8_t v_isExporting_903_; lean_object* v_entry_904_; lean_object* v___x_905_; lean_object* v_env_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_900_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_901_ = lean_st_ref_get(v___y_898_);
v_env_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_env_902_);
lean_dec(v___x_901_);
v_isExporting_903_ = lean_ctor_get_uint8(v_env_902_, sizeof(void*)*8);
lean_dec_ref(v_env_902_);
lean_inc(v_mod_890_);
v_entry_904_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_904_, 0, v_mod_890_);
lean_ctor_set_uint8(v_entry_904_, sizeof(void*)*1, v_isExporting_903_);
lean_ctor_set_uint8(v_entry_904_, sizeof(void*)*1 + 1, v_isMeta_891_);
v___x_905_ = lean_st_ref_get(v___y_898_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_906_);
lean_dec(v___x_905_);
v___x_907_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_908_ = lean_box(1);
v___x_909_ = lean_box(0);
v___x_953_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_900_, v___x_907_, v_env_906_, v___x_908_, v___x_909_);
v___x_954_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_953_, v_entry_904_);
lean_dec(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v_toCold_955_; lean_object* v_options_956_; uint8_t v_hasTrace_957_; 
v_toCold_955_ = lean_ctor_get(v___y_897_, 0);
v_options_956_ = lean_ctor_get(v_toCold_955_, 2);
v_hasTrace_957_ = lean_ctor_get_uint8(v_options_956_, sizeof(void*)*1);
if (v_hasTrace_957_ == 0)
{
lean_dec(v_hint_892_);
lean_dec(v_mod_890_);
v___y_911_ = v___y_896_;
v___y_912_ = v___y_898_;
goto v___jp_910_;
}
else
{
lean_object* v_inheritedTraceOptions_958_; lean_object* v_cls_959_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_inheritedTraceOptions_958_ = lean_ctor_get(v_toCold_955_, 11);
v_cls_959_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_979_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_958_, v_options_956_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v_hint_892_);
lean_dec(v_mod_890_);
v___y_911_ = v___y_896_;
v___y_912_ = v___y_898_;
goto v___jp_910_;
}
else
{
lean_object* v___x_981_; lean_object* v___y_983_; 
v___x_981_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_903_ == 0)
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_983_ = v___x_990_;
goto v___jp_982_;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_983_ = v___x_991_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_inc_ref(v___y_983_);
v___x_984_ = l_Lean_stringToMessageData(v___y_983_);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_981_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
if (v_isMeta_891_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_966_ = v___x_987_;
v___y_967_ = v___x_988_;
goto v___jp_965_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_966_ = v___x_987_;
v___y_967_ = v___x_989_;
goto v___jp_965_;
}
}
}
v___jp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___y_961_);
lean_ctor_set(v___x_963_, 1, v___y_962_);
v___x_964_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_959_, v___x_963_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_dec_ref_known(v___x_964_, 1);
v___y_911_ = v___y_896_;
v___y_912_ = v___y_898_;
goto v___jp_910_;
}
else
{
lean_dec_ref_known(v_entry_904_, 1);
return v___x_964_;
}
}
v___jp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
lean_inc_ref(v___y_967_);
v___x_968_ = l_Lean_stringToMessageData(v___y_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___y_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_MessageData_ofName(v_mod_890_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Name_isAnonymous(v_hint_892_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_976_ = l_Lean_MessageData_ofName(v_hint_892_);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___y_961_ = v___x_973_;
v___y_962_ = v___x_977_;
goto v___jp_960_;
}
else
{
lean_object* v___x_978_; 
lean_dec(v_hint_892_);
v___x_978_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_961_ = v___x_973_;
v___y_962_ = v___x_978_;
goto v___jp_960_;
}
}
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref_known(v_entry_904_, 1);
lean_dec(v_hint_892_);
lean_dec(v_mod_890_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
v___jp_910_:
{
lean_object* v___x_913_; lean_object* v_toEnvExtension_914_; lean_object* v_env_915_; lean_object* v_nextMacroScope_916_; lean_object* v_ngen_917_; lean_object* v_auxDeclNGen_918_; lean_object* v_traceState_919_; lean_object* v_recordedDeps_920_; lean_object* v_messages_921_; lean_object* v_infoState_922_; lean_object* v_snapshotTasks_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_951_; 
v___x_913_ = lean_st_ref_take(v___y_912_);
v_toEnvExtension_914_ = lean_ctor_get(v___x_907_, 0);
v_env_915_ = lean_ctor_get(v___x_913_, 0);
v_nextMacroScope_916_ = lean_ctor_get(v___x_913_, 1);
v_ngen_917_ = lean_ctor_get(v___x_913_, 2);
v_auxDeclNGen_918_ = lean_ctor_get(v___x_913_, 3);
v_traceState_919_ = lean_ctor_get(v___x_913_, 4);
v_recordedDeps_920_ = lean_ctor_get(v___x_913_, 6);
v_messages_921_ = lean_ctor_get(v___x_913_, 7);
v_infoState_922_ = lean_ctor_get(v___x_913_, 8);
v_snapshotTasks_923_ = lean_ctor_get(v___x_913_, 9);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_913_, 5);
lean_dec(v_unused_952_);
v___x_925_ = v___x_913_;
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snapshotTasks_923_);
lean_inc(v_infoState_922_);
lean_inc(v_messages_921_);
lean_inc(v_recordedDeps_920_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_918_);
lean_inc(v_ngen_917_);
lean_inc(v_nextMacroScope_916_);
lean_inc(v_env_915_);
lean_dec(v___x_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_asyncMode_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_asyncMode_927_ = lean_ctor_get(v_toEnvExtension_914_, 2);
v___x_928_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_907_, v_env_915_, v_entry_904_, v_asyncMode_927_, v___x_909_);
v___x_929_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 5, v___x_929_);
lean_ctor_set(v___x_925_, 0, v___x_928_);
v___x_931_ = v___x_925_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_nextMacroScope_916_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_ngen_917_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_auxDeclNGen_918_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_traceState_919_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_recordedDeps_920_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_messages_921_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_infoState_922_);
lean_ctor_set(v_reuseFailAlloc_950_, 9, v_snapshotTasks_923_);
v___x_931_ = v_reuseFailAlloc_950_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_mctx_934_; lean_object* v_zetaDeltaFVarIds_935_; lean_object* v_postponed_936_; lean_object* v_diag_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v___x_932_ = lean_st_ref_put(v___y_912_, v___x_931_);
v___x_933_ = lean_st_ref_take(v___y_911_);
v_mctx_934_ = lean_ctor_get(v___x_933_, 0);
v_zetaDeltaFVarIds_935_ = lean_ctor_get(v___x_933_, 2);
v_postponed_936_ = lean_ctor_get(v___x_933_, 3);
v_diag_937_ = lean_ctor_get(v___x_933_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_933_, 1);
lean_dec(v_unused_949_);
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_diag_937_);
lean_inc(v_postponed_936_);
lean_inc(v_zetaDeltaFVarIds_935_);
lean_inc(v_mctx_934_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_mctx_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_zetaDeltaFVarIds_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_postponed_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_diag_937_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_st_ref_put(v___y_911_, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_941_);
return v___x_946_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_994_, lean_object* v_isMeta_995_, lean_object* v_hint_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_isMeta_boxed_1004_; lean_object* v_res_1005_; 
v_isMeta_boxed_1004_ = lean_unbox(v_isMeta_995_);
v_res_1005_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_994_, v_isMeta_boxed_1004_, v_hint_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1006_, lean_object* v_declName_1007_, lean_object* v_as_1008_, size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec(v_declName_1007_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1011_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v_modules_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v_toImport_1026_; lean_object* v_module_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1021_ = l_Lean_Environment_header(v___x_1006_);
v_modules_1022_ = lean_ctor_get(v___x_1021_, 3);
lean_inc_ref(v_modules_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1024_ = lean_array_uget_borrowed(v_as_1008_, v_i_1010_);
v___x_1025_ = lean_array_get(v___x_1023_, v_modules_1022_, v_a_1024_);
lean_dec_ref(v_modules_1022_);
v_toImport_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_ref(v_toImport_1026_);
lean_dec(v___x_1025_);
v_module_1027_ = lean_ctor_get(v_toImport_1026_, 0);
lean_inc(v_module_1027_);
lean_dec_ref(v_toImport_1026_);
v___x_1028_ = lean_box(0);
v___x_1029_ = 0;
lean_inc(v_declName_1007_);
v___x_1030_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1027_, v___x_1029_, v_declName_1007_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1030_) == 0)
{
size_t v___x_1031_; size_t v___x_1032_; 
lean_dec_ref_known(v___x_1030_, 1);
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1010_, v___x_1031_);
v_i_1010_ = v___x_1032_;
v_b_1011_ = v___x_1028_;
goto _start;
}
else
{
lean_dec(v_declName_1007_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1034_, lean_object* v_declName_1035_, lean_object* v_as_1036_, lean_object* v_sz_1037_, lean_object* v_i_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_sz_boxed_1047_; size_t v_i_boxed_1048_; lean_object* v_res_1049_; 
v_sz_boxed_1047_ = lean_unbox_usize(v_sz_1037_);
lean_dec(v_sz_1037_);
v_i_boxed_1048_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1034_, v_declName_1035_, v_as_1036_, v_sz_boxed_1047_, v_i_boxed_1048_, v_b_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_as_1036_);
lean_dec_ref(v___x_1034_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1053_, uint8_t v_isMeta_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_env_1067_; lean_object* v___y_1069_; lean_object* v___x_1082_; 
v___x_1062_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1063_ = lean_st_ref_get(v___y_1060_);
v_env_1067_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_env_1067_);
lean_dec(v___x_1063_);
v___x_1082_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1067_, v_declName_1053_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec_ref(v_env_1067_);
lean_dec(v_declName_1053_);
goto v___jp_1064_;
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1084_; lean_object* v_modules_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l_Lean_Environment_header(v_env_1067_);
v_modules_1085_ = lean_ctor_get(v___x_1084_, 3);
lean_inc_ref(v_modules_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_array_get_size(v_modules_1085_);
v___x_1087_ = lean_nat_dec_lt(v_val_1083_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec_ref(v_modules_1085_);
lean_dec(v_val_1083_);
lean_dec_ref(v_env_1067_);
lean_dec(v_declName_1053_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___y_1091_; 
v___x_1088_ = lean_array_fget(v_modules_1085_, v_val_1083_);
lean_dec(v_val_1083_);
lean_dec_ref(v_modules_1085_);
v___x_1089_ = lean_st_ref_get(v___y_1060_);
if (v_isMeta_1054_ == 0)
{
lean_dec(v___x_1089_);
v___y_1091_ = v_isMeta_1054_;
goto v___jp_1090_;
}
else
{
lean_object* v_env_1102_; uint8_t v___x_1103_; 
v_env_1102_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1089_);
lean_inc(v_declName_1053_);
v___x_1103_ = l_Lean_isMarkedMeta(v_env_1102_, v_declName_1053_);
if (v___x_1103_ == 0)
{
v___y_1091_ = v_isMeta_1054_;
goto v___jp_1090_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = 0;
v___y_1091_ = v___x_1104_;
goto v___jp_1090_;
}
}
v___jp_1090_:
{
lean_object* v_toImport_1092_; lean_object* v_module_1093_; lean_object* v___x_1094_; 
v_toImport_1092_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_toImport_1092_);
lean_dec(v___x_1088_);
v_module_1093_ = lean_ctor_get(v_toImport_1092_, 0);
lean_inc(v_module_1093_);
lean_dec_ref(v_toImport_1092_);
lean_inc(v_declName_1053_);
v___x_1094_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1093_, v___y_1091_, v_declName_1053_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref_known(v___x_1094_, 1);
v___x_1095_ = l_Lean_indirectModUseExt;
v___x_1096_ = lean_box(1);
v___x_1097_ = lean_box(0);
lean_inc_ref(v_env_1067_);
v___x_1098_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1062_, v___x_1095_, v_env_1067_, v___x_1096_, v___x_1097_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1098_, v_declName_1053_);
lean_dec(v___x_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1069_ = v___x_1100_;
goto v___jp_1068_;
}
else
{
lean_object* v_val_1101_; 
v_val_1101_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v___x_1099_, 1);
v___y_1069_ = v_val_1101_;
goto v___jp_1068_;
}
}
else
{
lean_dec_ref(v_env_1067_);
lean_dec(v_declName_1053_);
return v___x_1094_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; size_t v_sz_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = lean_box(0);
v_sz_1071_ = lean_array_size(v___y_1069_);
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1067_, v_declName_1053_, v___y_1069_, v_sz_1071_, v___x_1072_, v___x_1070_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_env_1067_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1081_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1070_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1070_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1105_, lean_object* v_isMeta_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_isMeta_boxed_1114_; lean_object* v_res_1115_; 
v_isMeta_boxed_1114_ = lean_unbox(v_isMeta_1106_);
v_res_1115_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1105_, v_isMeta_boxed_1114_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
if (lean_obj_tag(v_as_x27_1116_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_b_1117_);
return v___x_1125_;
}
else
{
lean_object* v_head_1126_; lean_object* v_tail_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v_head_1126_ = lean_ctor_get(v_as_x27_1116_, 0);
v_tail_1127_ = lean_ctor_get(v_as_x27_1116_, 1);
v___x_1128_ = lean_box(0);
v___x_1129_ = 1;
lean_inc(v_head_1126_);
v___x_1130_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1126_, v___x_1129_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec_ref_known(v___x_1130_, 1);
v_as_x27_1116_ = v_tail_1127_;
v_b_1117_ = v___x_1128_;
goto _start;
}
else
{
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1132_, v_b_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v_as_x27_1132_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_currNamespace_1142_);
lean_ctor_set(v___x_1145_, 1, v___y_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1146_, v___y_1147_, v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1150_, lean_object* v___x_1151_, lean_object* v_currNamespace_1152_, lean_object* v_openDecls_1153_, lean_object* v_n_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = l_Lean_ResolveName_resolveGlobalName(v_env_1150_, v___x_1151_, v_currNamespace_1152_, v_openDecls_1153_, v_n_1154_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1159_, lean_object* v___x_1160_, lean_object* v_currNamespace_1161_, lean_object* v_openDecls_1162_, lean_object* v_n_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1159_, v___x_1160_, v_currNamespace_1161_, v_openDecls_1162_, v_n_1163_, v___y_1164_, v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v___x_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1167_, lean_object* v_currNamespace_1168_, lean_object* v_openDecls_1169_, lean_object* v_n_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_ResolveName_resolveNamespace(v_env_1167_, v_currNamespace_1168_, v_openDecls_1169_, v_n_1170_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___y_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1175_, lean_object* v_currNamespace_1176_, lean_object* v_openDecls_1177_, lean_object* v_n_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1175_, v_currNamespace_1176_, v_openDecls_1177_, v_n_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_toCold_1192_; lean_object* v_env_1193_; lean_object* v_currRecDepth_1194_; lean_object* v_ref_1195_; lean_object* v_maxRecDepth_1196_; lean_object* v_currNamespace_1197_; lean_object* v_openDecls_1198_; lean_object* v_quotContext_1199_; lean_object* v_currMacroScope_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v_methods_1207_; lean_object* v___x_1208_; lean_object* v_nextMacroScope_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1191_ = lean_st_ref_get(v___y_1189_);
v_toCold_1192_ = lean_ctor_get(v___y_1188_, 0);
v_env_1193_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref_n(v_env_1193_, 4);
lean_dec(v___x_1191_);
v_currRecDepth_1194_ = lean_ctor_get(v___y_1188_, 1);
v_ref_1195_ = lean_ctor_get(v___y_1188_, 2);
v_maxRecDepth_1196_ = lean_ctor_get(v_toCold_1192_, 3);
v_currNamespace_1197_ = lean_ctor_get(v_toCold_1192_, 4);
v_openDecls_1198_ = lean_ctor_get(v_toCold_1192_, 5);
v_quotContext_1199_ = lean_ctor_get(v_toCold_1192_, 8);
v_currMacroScope_1200_ = lean_ctor_get(v_toCold_1192_, 9);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1201_, 0, v_env_1193_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1202_, 0, v_env_1193_);
v___x_1203_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1188_);
lean_inc_n(v_currNamespace_1197_, 3);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1204_, 0, v_currNamespace_1197_);
lean_inc_n(v_openDecls_1198_, 2);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1205_, 0, v_env_1193_);
lean_closure_set(v___f_1205_, 1, v___x_1203_);
lean_closure_set(v___f_1205_, 2, v_currNamespace_1197_);
lean_closure_set(v___f_1205_, 3, v_openDecls_1198_);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1206_, 0, v_env_1193_);
lean_closure_set(v___f_1206_, 1, v_currNamespace_1197_);
lean_closure_set(v___f_1206_, 2, v_openDecls_1198_);
v_methods_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1207_, 0, v___f_1202_);
lean_ctor_set(v_methods_1207_, 1, v___f_1204_);
lean_ctor_set(v_methods_1207_, 2, v___f_1201_);
lean_ctor_set(v_methods_1207_, 3, v___f_1206_);
lean_ctor_set(v_methods_1207_, 4, v___f_1205_);
v___x_1208_ = lean_st_ref_get(v___y_1189_);
v_nextMacroScope_1209_ = lean_ctor_get(v___x_1208_, 1);
lean_inc(v_nextMacroScope_1209_);
lean_dec(v___x_1208_);
lean_inc(v_ref_1195_);
lean_inc(v_maxRecDepth_1196_);
lean_inc(v_currRecDepth_1194_);
lean_inc(v_currMacroScope_1200_);
lean_inc(v_quotContext_1199_);
v___x_1210_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1210_, 0, v_methods_1207_);
lean_ctor_set(v___x_1210_, 1, v_quotContext_1199_);
lean_ctor_set(v___x_1210_, 2, v_currMacroScope_1200_);
lean_ctor_set(v___x_1210_, 3, v_currRecDepth_1194_);
lean_ctor_set(v___x_1210_, 4, v_maxRecDepth_1196_);
lean_ctor_set(v___x_1210_, 5, v_ref_1195_);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_nextMacroScope_1209_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = lean_apply_2(v_x_1183_, v___x_1210_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v_macroScope_1216_; lean_object* v_traceMsgs_1217_; lean_object* v_expandedMacroDecls_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_a_1214_);
v_a_1215_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1213_, 2);
v_macroScope_1216_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_macroScope_1216_);
v_traceMsgs_1217_ = lean_ctor_get(v_a_1214_, 1);
lean_inc(v_traceMsgs_1217_);
v_expandedMacroDecls_1218_ = lean_ctor_get(v_a_1214_, 2);
lean_inc(v_expandedMacroDecls_1218_);
lean_dec(v_a_1214_);
v___x_1219_ = lean_box(0);
v___x_1220_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1218_, v___x_1219_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v_expandedMacroDecls_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_cache_1226_; lean_object* v_recordedDeps_1227_; lean_object* v_messages_1228_; lean_object* v_infoState_1229_; lean_object* v_snapshotTasks_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1221_ = lean_st_ref_take(v___y_1189_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
v_ngen_1223_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1221_, 4);
v_cache_1226_ = lean_ctor_get(v___x_1221_, 5);
v_recordedDeps_1227_ = lean_ctor_get(v___x_1221_, 6);
v_messages_1228_ = lean_ctor_get(v___x_1221_, 7);
v_infoState_1229_ = lean_ctor_get(v___x_1221_, 8);
v_snapshotTasks_1230_ = lean_ctor_get(v___x_1221_, 9);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1221_, 1);
lean_dec(v_unused_1257_);
v___x_1232_ = v___x_1221_;
v_isShared_1233_ = v_isSharedCheck_1256_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snapshotTasks_1230_);
lean_inc(v_infoState_1229_);
lean_inc(v_messages_1228_);
lean_inc(v_recordedDeps_1227_);
lean_inc(v_cache_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_env_1222_);
lean_dec(v___x_1221_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1256_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_macroScope_1216_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_env_1222_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_macroScope_1216_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1255_, 5, v_cache_1226_);
lean_ctor_set(v_reuseFailAlloc_1255_, 6, v_recordedDeps_1227_);
lean_ctor_set(v_reuseFailAlloc_1255_, 7, v_messages_1228_);
lean_ctor_set(v_reuseFailAlloc_1255_, 8, v_infoState_1229_);
lean_ctor_set(v_reuseFailAlloc_1255_, 9, v_snapshotTasks_1230_);
v___x_1235_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_st_ref_put(v___y_1189_, v___x_1235_);
v___x_1237_ = l_List_reverse___redArg(v_traceMsgs_1217_);
v___x_1238_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1237_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1238_, 0);
lean_dec(v_unused_1246_);
v___x_1240_ = v___x_1238_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v___x_1238_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v_a_1215_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1215_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_a_1215_);
v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1238_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1238_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_traceMsgs_1217_);
lean_dec(v_macroScope_1216_);
lean_dec(v_a_1215_);
v_a_1258_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1220_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1220_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1213_, 2);
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_a_1267_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_a_1267_);
v_a_1268_ = lean_ctor_get(v_a_1266_, 1);
lean_inc_ref(v_a_1268_);
lean_dec_ref_known(v_a_1266_, 2);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1270_ = lean_string_dec_eq(v_a_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1268_);
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
v___x_1273_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1267_, v___x_1272_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v_a_1267_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; 
lean_dec_ref(v_a_1268_);
v___x_1274_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1267_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_bs_1290_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_lt(v_i_1289_, v_sz_1288_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_bs_1290_);
return v___x_1292_;
}
else
{
lean_object* v_v_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_v_1293_ = lean_array_uget(v_bs_1290_, v_i_1289_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1293_);
v___x_1295_ = l_Lean_Syntax_isOfKind(v_v_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec(v_v_1293_);
lean_dec_ref(v_bs_1290_);
v___x_1296_ = lean_box(0);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = l_Lean_Syntax_getArg(v_v_1293_, v___x_1297_);
v___x_1299_ = l_Lean_Syntax_isOfKind(v___x_1298_, v___x_1294_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec(v_v_1293_);
lean_dec_ref(v_bs_1290_);
v___x_1300_ = lean_box(0);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v_bs_x27_1302_; lean_object* v___x_1303_; size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1301_ = lean_unsigned_to_nat(3u);
v_bs_x27_1302_ = lean_array_uset(v_bs_1290_, v_i_1289_, v___x_1297_);
v___x_1303_ = l_Lean_Syntax_getArg(v_v_1293_, v___x_1301_);
lean_dec(v_v_1293_);
v___x_1304_ = ((size_t)1ULL);
v___x_1305_ = lean_usize_add(v_i_1289_, v___x_1304_);
v___x_1306_ = lean_array_uset(v_bs_x27_1302_, v_i_1289_, v___x_1303_);
v_i_1289_ = v___x_1305_;
v_bs_1290_ = v___x_1306_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1308_, lean_object* v_i_1309_, lean_object* v_bs_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1308_);
lean_dec(v_sz_1308_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1311_, v_i_boxed_1312_, v_bs_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t v___x_1326_, size_t v_sz_1327_, size_t v_i_1328_, lean_object* v_bs_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_lt(v_i_1328_, v_sz_1327_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_bs_1329_);
return v___x_1331_;
}
else
{
lean_object* v_v_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_v_1332_ = lean_array_uget(v_bs_1329_, v_i_1328_);
v___x_1333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1332_);
v___x_1334_ = l_Lean_Syntax_isOfKind(v_v_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v_v_1332_);
lean_dec_ref(v_bs_1329_);
v___x_1335_ = lean_box(0);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_bs_x27_1338_; 
v___x_1336_ = lean_unsigned_to_nat(3u);
v___x_1337_ = lean_unsigned_to_nat(0u);
v_bs_x27_1338_ = lean_array_uset(v_bs_1329_, v_i_1328_, v___x_1337_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = l_Lean_Syntax_getArg(v_v_1332_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1348_ = l_Lean_Syntax_isOfKind(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref(v_bs_x27_1338_);
lean_dec(v_v_1332_);
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
else
{
goto v___jp_1339_;
}
}
else
{
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = l_Lean_Syntax_getArg(v_v_1332_, v___x_1336_);
lean_dec(v_v_1332_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1328_, v___x_1341_);
v___x_1343_ = lean_array_uset(v_bs_x27_1338_, v_i_1328_, v___x_1340_);
v_i_1328_ = v___x_1342_;
v_bs_1329_ = v___x_1343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v___x_1350_, lean_object* v_sz_1351_, lean_object* v_i_1352_, lean_object* v_bs_1353_){
_start:
{
uint8_t v___x_177019__boxed_1354_; size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v___x_177019__boxed_1354_ = lean_unbox(v___x_1350_);
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1351_);
lean_dec(v_sz_1351_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1352_);
lean_dec(v_i_1352_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_177019__boxed_1354_, v_sz_boxed_1355_, v_i_boxed_1356_, v_bs_1353_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1364_, size_t v_i_1365_, lean_object* v_bs_1366_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_usize_dec_lt(v_i_1365_, v_sz_1364_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_bs_1366_);
return v___x_1368_;
}
else
{
lean_object* v_v_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_v_1369_ = lean_array_uget(v_bs_1366_, v_i_1365_);
v___x_1370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1369_);
v___x_1371_ = l_Lean_Syntax_isOfKind(v_v_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v_v_1369_);
lean_dec_ref(v_bs_1366_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v_bs_x27_1374_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v_bs_x27_1374_ = lean_array_uset(v_bs_1366_, v_i_1365_, v___x_1373_);
v___x_1381_ = l_Lean_Syntax_getArg(v_v_1369_, v___x_1373_);
lean_dec(v_v_1369_);
v___x_1382_ = l_Lean_Syntax_isNone(v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = lean_unsigned_to_nat(2u);
v___x_1384_ = l_Lean_Syntax_matchesNull(v___x_1381_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec_ref(v_bs_x27_1374_);
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
else
{
goto v___jp_1375_;
}
}
else
{
lean_dec(v___x_1381_);
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1365_, v___x_1377_);
v___x_1379_ = lean_array_uset(v_bs_x27_1374_, v_i_1365_, v___x_1376_);
v_i_1365_ = v___x_1378_;
v_bs_1366_ = v___x_1379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1386_, lean_object* v_i_1387_, lean_object* v_bs_1388_){
_start:
{
size_t v_sz_boxed_1389_; size_t v_i_boxed_1390_; lean_object* v_res_1391_; 
v_sz_boxed_1389_ = lean_unbox_usize(v_sz_1386_);
lean_dec(v_sz_1386_);
v_i_boxed_1390_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1389_, v_i_boxed_1390_, v_bs_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1392_, size_t v_i_1393_, lean_object* v_bs_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1393_, v_sz_1392_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_bs_1394_);
return v___x_1396_;
}
else
{
lean_object* v_v_1397_; lean_object* v___x_1398_; lean_object* v_bs_x27_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_v_1397_ = lean_array_uget(v_bs_1394_, v_i_1393_);
v___x_1398_ = lean_unsigned_to_nat(0u);
v_bs_x27_1399_ = lean_array_uset(v_bs_1394_, v_i_1393_, v___x_1398_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_i_1393_, v___x_1400_);
v___x_1402_ = lean_array_uset(v_bs_x27_1399_, v_i_1393_, v_v_1397_);
v_i_1393_ = v___x_1401_;
v_bs_1394_ = v___x_1402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1404_, lean_object* v_i_1405_, lean_object* v_bs_1406_){
_start:
{
size_t v_sz_boxed_1407_; size_t v_i_boxed_1408_; lean_object* v_res_1409_; 
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1404_);
lean_dec(v_sz_1404_);
v_i_boxed_1408_ = lean_unbox_usize(v_i_1405_);
lean_dec(v_i_1405_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1407_, v_i_boxed_1408_, v_bs_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1411_, v___y_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1415_, v_x_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_x_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1423_, lean_object* v_as_x27_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
if (lean_obj_tag(v_as_x27_1424_) == 0)
{
lean_object* v___x_1433_; 
lean_dec(v_stx_1423_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1425_);
return v___x_1433_;
}
else
{
lean_object* v_head_1434_; lean_object* v_tail_1435_; lean_object* v_value_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_b_1425_);
v_head_1434_ = lean_ctor_get(v_as_x27_1424_, 0);
v_tail_1435_ = lean_ctor_get(v_as_x27_1424_, 1);
v_value_1436_ = lean_ctor_get(v_head_1434_, 1);
v___x_1437_ = lean_box(0);
v___x_1438_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1439_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1436_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v_stx_1423_);
v___x_1440_ = lean_apply_8(v_value_1436_, v_stx_1423_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, lean_box(0));
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_stx_1423_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1450_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1450_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_a_1441_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1437_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1446_);
v___x_1448_ = v___x_1443_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1471_; 
v_a_1451_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1453_ = v___x_1440_;
v_isShared_1454_ = v_isSharedCheck_1471_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1440_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1471_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
uint8_t v___y_1456_; uint8_t v___x_1469_; 
v___x_1469_ = l_Lean_Exception_isInterrupt(v_a_1451_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
lean_inc(v_a_1451_);
v___x_1470_ = l_Lean_Exception_isRuntime(v_a_1451_);
v___y_1456_ = v___x_1470_;
goto v___jp_1455_;
}
else
{
v___y_1456_ = v___x_1469_;
goto v___jp_1455_;
}
v___jp_1455_:
{
if (v___y_1456_ == 0)
{
if (lean_obj_tag(v_a_1451_) == 0)
{
lean_object* v___x_1458_; 
lean_dec(v_stx_1423_);
if (v_isShared_1454_ == 0)
{
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1451_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v_id_1460_; uint8_t v___x_1461_; 
v_id_1460_ = lean_ctor_get(v_a_1451_, 0);
v___x_1461_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1439_, v_id_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_stx_1423_);
if (v_isShared_1454_ == 0)
{
v___x_1463_ = v___x_1453_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1451_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_dec_ref_known(v_a_1451_, 2);
lean_del_object(v___x_1453_);
v_as_x27_1424_ = v_tail_1435_;
v_b_1425_ = v___x_1438_;
goto _start;
}
}
}
else
{
lean_object* v___x_1467_; 
lean_dec(v_stx_1423_);
if (v_isShared_1454_ == 0)
{
v___x_1467_ = v___x_1453_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1451_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1472_, lean_object* v_as_x27_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1472_, v_as_x27_1473_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_as_x27_1473_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1485_, lean_object* v_rhs_x3f_1486_, lean_object* v_otherwise_x3f_1487_, lean_object* v_body_x3f_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
uint8_t v___y_1497_; lean_object* v___y_1498_; uint8_t v___y_1499_; uint8_t v___y_1500_; uint8_t v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v_body_1508_; lean_object* v___y_1529_; lean_object* v_otherwise_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v_rhs_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; 
if (lean_obj_tag(v_rhs_x3f_1486_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1542_ = v___x_1553_;
v___y_1543_ = v_a_1489_;
v___y_1544_ = v_a_1490_;
v___y_1545_ = v_a_1491_;
v___y_1546_ = v_a_1492_;
v___y_1547_ = v_a_1493_;
v___y_1548_ = v_a_1494_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1555_; 
v_val_1554_ = lean_ctor_get(v_rhs_x3f_1486_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v_rhs_x3f_1486_, 1);
v___x_1555_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1554_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_rhs_1542_ = v_a_1556_;
v___y_1543_ = v_a_1489_;
v___y_1544_ = v_a_1490_;
v___y_1545_ = v_a_1491_;
v___y_1546_ = v_a_1492_;
v___y_1547_ = v_a_1493_;
v___y_1548_ = v_a_1494_;
goto v___jp_1541_;
}
else
{
lean_dec(v_body_x3f_1488_);
lean_dec(v_otherwise_x3f_1487_);
lean_dec_ref(v_reassigned_1485_);
return v___x_1555_;
}
}
v___jp_1496_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1503_, 0, v___y_1498_);
lean_ctor_set(v___x_1503_, 1, v___y_1502_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*2, v___y_1499_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*2 + 1, v___y_1501_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*2 + 2, v___y_1500_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*2 + 3, v___y_1497_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
v___jp_1505_:
{
lean_object* v___x_1509_; lean_object* v_info_1510_; uint8_t v_breaks_1511_; uint8_t v_continues_1512_; uint8_t v_returnsEarly_1513_; lean_object* v_numRegularExits_1514_; uint8_t v_noFallthrough_1515_; lean_object* v_reassigns_1516_; size_t v_sz_1517_; size_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1509_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1508_, v___y_1506_);
v_info_1510_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1507_, v___x_1509_);
v_breaks_1511_ = lean_ctor_get_uint8(v_info_1510_, sizeof(void*)*2);
v_continues_1512_ = lean_ctor_get_uint8(v_info_1510_, sizeof(void*)*2 + 1);
v_returnsEarly_1513_ = lean_ctor_get_uint8(v_info_1510_, sizeof(void*)*2 + 2);
v_numRegularExits_1514_ = lean_ctor_get(v_info_1510_, 0);
lean_inc(v_numRegularExits_1514_);
v_noFallthrough_1515_ = lean_ctor_get_uint8(v_info_1510_, sizeof(void*)*2 + 3);
v_reassigns_1516_ = lean_ctor_get(v_info_1510_, 1);
lean_inc(v_reassigns_1516_);
lean_dec_ref(v_info_1510_);
v_sz_1517_ = lean_array_size(v_reassigned_1485_);
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1517_, v___x_1518_, v_reassigned_1485_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_array_get_size(v___x_1519_);
v___x_1522_ = lean_nat_dec_lt(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_dec_ref(v___x_1519_);
v___y_1497_ = v_noFallthrough_1515_;
v___y_1498_ = v_numRegularExits_1514_;
v___y_1499_ = v_breaks_1511_;
v___y_1500_ = v_returnsEarly_1513_;
v___y_1501_ = v_continues_1512_;
v___y_1502_ = v_reassigns_1516_;
goto v___jp_1496_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_nat_dec_le(v___x_1521_, v___x_1521_);
if (v___x_1523_ == 0)
{
if (v___x_1522_ == 0)
{
lean_dec_ref(v___x_1519_);
v___y_1497_ = v_noFallthrough_1515_;
v___y_1498_ = v_numRegularExits_1514_;
v___y_1499_ = v_breaks_1511_;
v___y_1500_ = v_returnsEarly_1513_;
v___y_1501_ = v_continues_1512_;
v___y_1502_ = v_reassigns_1516_;
goto v___jp_1496_;
}
else
{
size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_usize_of_nat(v___x_1521_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1519_, v___x_1518_, v___x_1524_, v_reassigns_1516_);
lean_dec_ref(v___x_1519_);
v___y_1497_ = v_noFallthrough_1515_;
v___y_1498_ = v_numRegularExits_1514_;
v___y_1499_ = v_breaks_1511_;
v___y_1500_ = v_returnsEarly_1513_;
v___y_1501_ = v_continues_1512_;
v___y_1502_ = v___x_1525_;
goto v___jp_1496_;
}
}
else
{
size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_usize_of_nat(v___x_1521_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1519_, v___x_1518_, v___x_1526_, v_reassigns_1516_);
lean_dec_ref(v___x_1519_);
v___y_1497_ = v_noFallthrough_1515_;
v___y_1498_ = v_numRegularExits_1514_;
v___y_1499_ = v_breaks_1511_;
v___y_1500_ = v_returnsEarly_1513_;
v___y_1501_ = v_continues_1512_;
v___y_1502_ = v___x_1527_;
goto v___jp_1496_;
}
}
}
v___jp_1528_:
{
if (lean_obj_tag(v_body_x3f_1488_) == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1506_ = v_otherwise_1530_;
v___y_1507_ = v___y_1529_;
v_body_1508_ = v___x_1537_;
goto v___jp_1505_;
}
else
{
lean_object* v_val_1538_; lean_object* v___x_1539_; 
v_val_1538_ = lean_ctor_get(v_body_x3f_1488_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v_body_x3f_1488_, 1);
v___x_1539_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1538_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___y_1506_ = v_otherwise_1530_;
v___y_1507_ = v___y_1529_;
v_body_1508_ = v_a_1540_;
goto v___jp_1505_;
}
else
{
lean_dec_ref(v_otherwise_1530_);
lean_dec_ref(v___y_1529_);
lean_dec_ref(v_reassigned_1485_);
return v___x_1539_;
}
}
}
v___jp_1541_:
{
if (lean_obj_tag(v_otherwise_x3f_1487_) == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1529_ = v_rhs_1542_;
v_otherwise_1530_ = v___x_1549_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1545_;
v___y_1534_ = v___y_1546_;
v___y_1535_ = v___y_1547_;
v___y_1536_ = v___y_1548_;
goto v___jp_1528_;
}
else
{
lean_object* v_val_1550_; lean_object* v___x_1551_; 
v_val_1550_ = lean_ctor_get(v_otherwise_x3f_1487_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v_otherwise_x3f_1487_, 1);
v___x_1551_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1550_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___y_1529_ = v_rhs_1542_;
v_otherwise_1530_ = v_a_1552_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1545_;
v___y_1534_ = v___y_1546_;
v___y_1535_ = v___y_1547_;
v___y_1536_ = v___y_1548_;
goto v___jp_1528_;
}
else
{
lean_dec_ref(v_rhs_1542_);
lean_dec(v_body_x3f_1488_);
lean_dec_ref(v_reassigned_1485_);
return v___x_1551_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18));
v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1659_, lean_object* v_decl_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v_reassigns_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1660_);
v___x_1697_ = l_Lean_Syntax_isOfKind(v_decl_1660_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1660_);
v___x_1699_ = l_Lean_Syntax_isOfKind(v_decl_1660_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1700_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1701_ = lean_box(0);
v___x_1702_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1701_, v___x_1699_);
v___x_1703_ = l_Std_Format_defWidth;
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = l_Std_Format_pretty(v___x_1702_, v___x_1703_, v___x_1704_, v___x_1704_);
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1700_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1707_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; lean_object* v_pattern_1710_; lean_object* v___y_1712_; lean_object* v_otherwise_x3f_1713_; lean_object* v_body_x3f_x3f_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_body_x3f_x3f_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___x_1744_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1709_ = lean_unsigned_to_nat(0u);
v_pattern_1710_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1709_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1783_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1744_);
v___x_1784_ = l_Lean_Syntax_isNone(v___x_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc(v___x_1783_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1744_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v___x_1783_);
lean_dec(v_pattern_1710_);
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1787_ = lean_box(0);
v___x_1788_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1787_, v___x_1785_);
v___x_1789_ = l_Std_Format_defWidth;
v___x_1790_ = l_Std_Format_pretty(v___x_1788_, v___x_1789_, v___x_1709_, v___x_1709_);
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1786_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1792_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1709_);
lean_dec(v___x_1783_);
v___x_1795_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_pattern_1710_);
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1798_ = lean_box(0);
v___x_1799_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1798_, v___x_1796_);
v___x_1800_ = l_Std_Format_defWidth;
v___x_1801_ = l_Std_Format_pretty(v___x_1799_, v___x_1800_, v___x_1709_, v___x_1709_);
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1797_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1803_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1804_;
}
else
{
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
v___y_1749_ = v_a_1664_;
v___y_1750_ = v_a_1665_;
v___y_1751_ = v_a_1666_;
goto v___jp_1745_;
}
}
}
else
{
lean_dec(v___x_1783_);
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
v___y_1749_ = v_a_1664_;
v___y_1750_ = v_a_1665_;
v___y_1751_ = v_a_1666_;
goto v___jp_1745_;
}
v___jp_1711_:
{
if (v_reassignment_1659_ == 0)
{
lean_object* v___x_1721_; 
lean_dec(v_pattern_1710_);
v___x_1721_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1681_ = v___y_1712_;
v___y_1682_ = v_otherwise_x3f_1713_;
v___y_1683_ = v_body_x3f_x3f_1714_;
v_reassigns_1684_ = v___x_1721_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
v___y_1688_ = v___y_1718_;
v___y_1689_ = v___y_1719_;
v___y_1690_ = v___y_1720_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1710_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___y_1681_ = v___y_1712_;
v___y_1682_ = v_otherwise_x3f_1713_;
v___y_1683_ = v_body_x3f_x3f_1714_;
v_reassigns_1684_ = v_a_1723_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
v___y_1688_ = v___y_1718_;
v___y_1689_ = v___y_1719_;
v___y_1690_ = v___y_1720_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_body_x3f_x3f_1714_);
lean_dec(v_otherwise_x3f_1713_);
lean_dec(v___y_1712_);
v_a_1724_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1722_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
v___jp_1732_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1733_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_body_x3f_x3f_1735_);
v___y_1712_ = v___y_1734_;
v_otherwise_x3f_1713_ = v___x_1742_;
v_body_x3f_x3f_1714_ = v___x_1743_;
v___y_1715_ = v___y_1736_;
v___y_1716_ = v___y_1737_;
v___y_1717_ = v___y_1738_;
v___y_1718_ = v___y_1739_;
v___y_1719_ = v___y_1740_;
v___y_1720_ = v___y_1741_;
goto v___jp_1711_;
}
v___jp_1745_:
{
lean_object* v___x_1752_; lean_object* v_rhs_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1752_ = lean_unsigned_to_nat(3u);
v_rhs_1753_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(4u);
v___x_1755_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1754_);
v___x_1756_ = l_Lean_Syntax_isNone(v___x_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; 
lean_inc(v___x_1755_);
v___x_1757_ = l_Lean_Syntax_matchesNull(v___x_1755_, v___x_1752_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1755_);
lean_dec(v_rhs_1753_);
lean_dec(v_pattern_1710_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1759_, v___x_1757_);
v___x_1761_ = l_Std_Format_defWidth;
v___x_1762_ = l_Std_Format_pretty(v___x_1760_, v___x_1761_, v___x_1709_, v___x_1709_);
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1758_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1764_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v_otherwise_x3f_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1766_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1767_ = l_Lean_Syntax_getArg(v___x_1755_, v___x_1744_);
v___x_1768_ = l_Lean_Syntax_getArg(v___x_1755_, v___x_1766_);
lean_dec(v___x_1755_);
v___x_1769_ = l_Lean_Syntax_isNone(v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
lean_inc(v___x_1768_);
v___x_1770_ = l_Lean_Syntax_matchesNull(v___x_1768_, v___x_1744_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec(v___x_1768_);
lean_dec(v_otherwise_x3f_1767_);
lean_dec(v_rhs_1753_);
lean_dec(v_pattern_1710_);
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1772_, v___x_1770_);
v___x_1774_ = l_Std_Format_defWidth;
v___x_1775_ = l_Std_Format_pretty(v___x_1773_, v___x_1774_, v___x_1709_, v___x_1709_);
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1771_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1777_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1778_;
}
else
{
lean_object* v_body_x3f_x3f_1779_; lean_object* v___x_1780_; 
lean_dec(v_decl_1660_);
v_body_x3f_x3f_1779_ = l_Lean_Syntax_getArg(v___x_1768_, v___x_1709_);
lean_dec(v___x_1768_);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_body_x3f_x3f_1779_);
v___y_1733_ = v_otherwise_x3f_1767_;
v___y_1734_ = v_rhs_1753_;
v_body_x3f_x3f_1735_ = v___x_1780_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
v___y_1739_ = v___y_1749_;
v___y_1740_ = v___y_1750_;
v___y_1741_ = v___y_1751_;
goto v___jp_1732_;
}
}
else
{
lean_object* v___x_1781_; 
lean_dec(v___x_1768_);
lean_dec(v_decl_1660_);
v___x_1781_ = lean_box(0);
v___y_1733_ = v_otherwise_x3f_1767_;
v___y_1734_ = v_rhs_1753_;
v_body_x3f_x3f_1735_ = v___x_1781_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
v___y_1739_ = v___y_1749_;
v___y_1740_ = v___y_1750_;
v___y_1741_ = v___y_1751_;
goto v___jp_1732_;
}
}
}
else
{
lean_object* v___x_1782_; 
lean_dec(v___x_1755_);
lean_dec(v_decl_1660_);
v___x_1782_ = lean_box(0);
v___y_1712_ = v_rhs_1753_;
v_otherwise_x3f_1713_ = v___x_1782_;
v_body_x3f_x3f_1714_ = v___x_1782_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1747_;
v___y_1717_ = v___y_1748_;
v___y_1718_ = v___y_1749_;
v___y_1719_ = v___y_1750_;
v___y_1720_ = v___y_1751_;
goto v___jp_1711_;
}
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v_x_1806_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1805_ = lean_unsigned_to_nat(0u);
v_x_1806_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1805_);
v___x_1820_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1806_);
v___x_1821_ = l_Lean_Syntax_isOfKind(v_x_1806_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_x_1806_);
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1823_, v___x_1821_);
v___x_1825_ = l_Std_Format_defWidth;
v___x_1826_ = l_Std_Format_pretty(v___x_1824_, v___x_1825_, v___x_1805_, v___x_1805_);
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1822_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1828_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1830_);
v___x_1832_ = l_Lean_Syntax_isNone(v___x_1831_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
lean_inc(v___x_1831_);
v___x_1833_ = l_Lean_Syntax_matchesNull(v___x_1831_, v___x_1830_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v___x_1831_);
lean_dec(v_x_1806_);
v___x_1834_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1835_, v___x_1833_);
v___x_1837_ = l_Std_Format_defWidth;
v___x_1838_ = l_Std_Format_pretty(v___x_1836_, v___x_1837_, v___x_1805_, v___x_1805_);
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1834_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1840_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = l_Lean_Syntax_getArg(v___x_1831_, v___x_1805_);
lean_dec(v___x_1831_);
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1844_ = l_Lean_Syntax_isOfKind(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_x_1806_);
v___x_1845_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_Syntax_formatStx(v_decl_1660_, v___x_1846_, v___x_1844_);
v___x_1848_ = l_Std_Format_defWidth;
v___x_1849_ = l_Std_Format_pretty(v___x_1847_, v___x_1848_, v___x_1805_, v___x_1805_);
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1845_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1851_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1852_;
}
else
{
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
v___y_1811_ = v_a_1664_;
v___y_1812_ = v_a_1665_;
v___y_1813_ = v_a_1666_;
goto v___jp_1807_;
}
}
}
else
{
lean_dec(v___x_1831_);
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
v___y_1811_ = v_a_1664_;
v___y_1812_ = v_a_1665_;
v___y_1813_ = v_a_1666_;
goto v___jp_1807_;
}
}
v___jp_1807_:
{
lean_object* v___x_1814_; lean_object* v_rhs_1815_; 
v___x_1814_ = lean_unsigned_to_nat(3u);
v_rhs_1815_ = l_Lean_Syntax_getArg(v_decl_1660_, v___x_1814_);
lean_dec(v_decl_1660_);
if (v_reassignment_1659_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_x_1806_);
v___x_1816_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1669_ = v___y_1808_;
v___y_1670_ = v___y_1813_;
v___y_1671_ = v___y_1812_;
v___y_1672_ = v_rhs_1815_;
v___y_1673_ = v___y_1809_;
v___y_1674_ = v___y_1810_;
v___y_1675_ = v___y_1811_;
v___y_1676_ = v___x_1816_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = lean_mk_empty_array_with_capacity(v___x_1817_);
v___x_1819_ = lean_array_push(v___x_1818_, v_x_1806_);
v___y_1669_ = v___y_1808_;
v___y_1670_ = v___y_1813_;
v___y_1671_ = v___y_1812_;
v___y_1672_ = v_rhs_1815_;
v___y_1673_ = v___y_1809_;
v___y_1674_ = v___y_1810_;
v___y_1675_ = v___y_1811_;
v___y_1676_ = v___x_1819_;
goto v___jp_1668_;
}
}
}
v___jp_1668_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1672_);
v___x_1678_ = lean_box(0);
v___x_1679_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1676_, v___x_1677_, v___x_1678_, v___x_1678_, v___y_1669_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1671_, v___y_1670_);
return v___x_1679_;
}
v___jp_1680_:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1681_);
if (lean_obj_tag(v___y_1683_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_box(0);
v___x_1693_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1684_, v___x_1691_, v___y_1682_, v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1693_;
}
else
{
lean_object* v_val_1694_; lean_object* v___x_1695_; 
v_val_1694_ = lean_ctor_get(v___y_1683_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v___y_1683_, 1);
v___x_1695_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1684_, v___x_1691_, v___y_1682_, v_val_1694_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1978_, size_t v_sz_1979_, size_t v_i_1980_, lean_object* v_b_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_usize_dec_lt(v_i_1980_, v_sz_1979_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_b_1981_);
return v___x_1990_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_array_uget_borrowed(v_as_1978_, v_i_1980_);
lean_inc(v_a_1991_);
v___x_1992_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1991_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; size_t v___x_1995_; size_t v___x_1996_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1993_, v_b_1981_);
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1980_, v___x_1995_);
v_i_1980_ = v___x_1996_;
v_b_1981_ = v___x_1994_;
goto _start;
}
else
{
lean_dec_ref(v_b_1981_);
return v___x_1992_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2027_, lean_object* v_as_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_a_2040_; uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_b_2031_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v_a_2047_; uint8_t v___x_2048_; 
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2047_ = lean_array_uget_borrowed(v_as_2028_, v_i_2030_);
lean_inc(v_a_2047_);
v___x_2048_ = l_Lean_Syntax_isOfKind(v_a_2047_, v___x_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref_known(v___x_2049_, 1);
v_a_2040_ = v_b_2031_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_b_2031_);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
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
}
else
{
lean_object* v___x_2058_; lean_object* v___y_2060_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2058_ = lean_unsigned_to_nat(3u);
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = l_Lean_Syntax_getArg(v_a_2047_, v___x_2077_);
v___x_2079_ = l_Lean_Syntax_getArgs(v___x_2078_);
lean_dec(v___x_2078_);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2082_ = lean_array_get_size(v___x_2079_);
v___x_2083_ = lean_nat_dec_lt(v___x_2080_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v___x_2079_);
v___y_2060_ = v___x_2081_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v_snd_2089_; 
v___x_2084_ = lean_box(v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2081_);
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___x_2082_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2048_, v___x_2027_, v___x_2079_, v___x_2086_, v___x_2087_, v___x_2085_);
lean_dec_ref(v___x_2079_);
v_snd_2089_ = lean_ctor_get(v___x_2088_, 1);
lean_inc(v_snd_2089_);
lean_dec_ref(v___x_2088_);
v___y_2060_ = v_snd_2089_;
goto v___jp_2059_;
}
v___jp_2059_:
{
size_t v_sz_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_sz_2061_ = lean_array_size(v___y_2060_);
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2061_, v___x_2062_, v___y_2060_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_dec_ref_known(v___x_2064_, 1);
v_a_2040_ = v_b_2031_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_b_2031_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref_known(v___x_2063_, 1);
v___x_2073_ = l_Lean_Syntax_getArg(v_a_2047_, v___x_2058_);
v___x_2074_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2073_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2031_, v_a_2075_);
v_a_2040_ = v___x_2076_;
goto v___jp_2039_;
}
else
{
lean_dec_ref(v_b_2031_);
return v___x_2074_;
}
}
}
}
}
v___jp_2039_:
{
size_t v___x_2041_; size_t v___x_2042_; 
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2030_, v___x_2041_);
v_i_2030_ = v___x_2042_;
v_b_2031_ = v_a_2040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2090_, size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_a_2102_; uint8_t v___x_2106_; 
v___x_2106_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_b_2093_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v_a_2109_ = lean_array_uget_borrowed(v_as_2090_, v_i_2092_);
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2109_);
v___x_2123_ = l_Lean_Syntax_isOfKind(v_a_2109_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2109_);
v___x_2125_ = l_Lean_Syntax_isOfKind(v_a_2109_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2127_ = lean_box(0);
lean_inc(v_a_2109_);
v___x_2128_ = l_Lean_Syntax_formatStx(v_a_2109_, v___x_2127_, v___x_2125_);
v___x_2129_ = l_Std_Format_defWidth;
v___x_2130_ = l_Std_Format_pretty(v___x_2128_, v___x_2129_, v___x_2108_, v___x_2108_);
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2126_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2132_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref_known(v___x_2133_, 1);
v_a_2102_ = v_b_2093_;
goto v___jp_2101_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_b_2093_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = l_Lean_Syntax_getArg(v_a_2109_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2143_);
v___x_2145_ = l_Lean_Syntax_isOfKind(v___x_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v___x_2143_);
v___x_2146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2147_ = lean_box(0);
lean_inc(v_a_2109_);
v___x_2148_ = l_Lean_Syntax_formatStx(v_a_2109_, v___x_2147_, v___x_2145_);
v___x_2149_ = l_Std_Format_defWidth;
v___x_2150_ = l_Std_Format_pretty(v___x_2148_, v___x_2149_, v___x_2108_, v___x_2108_);
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2146_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2152_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec_ref_known(v___x_2153_, 1);
v_a_2102_ = v_b_2093_;
goto v___jp_2101_;
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_b_2093_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2162_ = l_Lean_Syntax_getArg(v___x_2143_, v___x_2108_);
lean_dec(v___x_2143_);
v___x_2163_ = l_Lean_Syntax_getArgs(v___x_2162_);
lean_dec(v___x_2162_);
v_sz_2164_ = lean_array_size(v___x_2163_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2123_, v___x_2163_, v_sz_2164_, v___x_2165_, v_b_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec_ref(v___x_2163_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v_a_2102_ = v_a_2167_;
goto v___jp_2101_;
}
else
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(2u);
v___x_2169_ = l_Lean_Syntax_getArg(v_a_2109_, v___x_2168_);
v___x_2170_ = l_Lean_Syntax_isNone(v___x_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
v___x_2171_ = l_Lean_Syntax_matchesNull(v___x_2169_, v___x_2168_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2172_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2173_ = lean_box(0);
lean_inc(v_a_2109_);
v___x_2174_ = l_Lean_Syntax_formatStx(v_a_2109_, v___x_2173_, v___x_2171_);
v___x_2175_ = l_Std_Format_defWidth;
v___x_2176_ = l_Std_Format_pretty(v___x_2174_, v___x_2175_, v___x_2108_, v___x_2108_);
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2172_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2178_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_dec_ref_known(v___x_2179_, 1);
v_a_2102_ = v_b_2093_;
goto v___jp_2101_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_b_2093_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
v___y_2111_ = v___y_2094_;
v___y_2112_ = v___y_2095_;
v___y_2113_ = v___y_2096_;
v___y_2114_ = v___y_2097_;
v___y_2115_ = v___y_2098_;
v___y_2116_ = v___y_2099_;
goto v___jp_2110_;
}
}
else
{
lean_dec(v___x_2169_);
v___y_2111_ = v___y_2094_;
v___y_2112_ = v___y_2095_;
v___y_2113_ = v___y_2096_;
v___y_2114_ = v___y_2097_;
v___y_2115_ = v___y_2098_;
v___y_2116_ = v___y_2099_;
goto v___jp_2110_;
}
}
v___jp_2110_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(4u);
v___x_2118_ = l_Lean_Syntax_getArg(v_a_2109_, v___x_2117_);
v___x_2119_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2118_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2120_, v_b_2093_);
v_a_2102_ = v___x_2121_;
goto v___jp_2101_;
}
else
{
lean_dec_ref(v_b_2093_);
return v___x_2119_;
}
}
}
v___jp_2101_:
{
size_t v___x_2103_; size_t v___x_2104_; 
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_i_2092_, v___x_2103_);
v_i_2092_ = v___x_2104_;
v_b_2093_ = v_a_2102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2188_) == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2199_; 
v_val_2198_ = lean_ctor_get(v_stx_x3f_2188_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_stx_x3f_2188_, 1);
v___x_2199_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2198_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2218_, lean_object* v_as_2219_, size_t v_sz_2220_, size_t v_i_2221_, lean_object* v_b_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_a_2231_; uint8_t v___x_2235_; 
v___x_2235_ = lean_usize_dec_lt(v_i_2221_, v_sz_2220_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_b_2222_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v_a_2238_; uint8_t v___x_2239_; 
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2238_ = lean_array_uget_borrowed(v_as_2219_, v_i_2221_);
lean_inc(v_a_2238_);
v___x_2239_ = l_Lean_Syntax_isOfKind(v_a_2238_, v___x_2237_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_dec_ref_known(v___x_2240_, 1);
v_a_2231_ = v_b_2222_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v_b_2222_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v___y_2251_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2249_ = lean_unsigned_to_nat(3u);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = l_Lean_Syntax_getArg(v_a_2238_, v___x_2268_);
v___x_2270_ = l_Lean_Syntax_getArgs(v___x_2269_);
lean_dec(v___x_2269_);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2273_ = lean_array_get_size(v___x_2270_);
v___x_2274_ = lean_nat_dec_lt(v___x_2271_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v___x_2270_);
v___y_2251_ = v___x_2272_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; lean_object* v_snd_2280_; 
v___x_2275_ = lean_box(v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2272_);
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2273_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2239_, v___x_2218_, v___x_2270_, v___x_2277_, v___x_2278_, v___x_2276_);
lean_dec_ref(v___x_2270_);
v_snd_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2279_);
v___y_2251_ = v_snd_2280_;
goto v___jp_2250_;
}
v___jp_2250_:
{
size_t v_sz_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v_sz_2252_ = lean_array_size(v___y_2251_);
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2252_, v___x_2253_, v___y_2251_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref_known(v___x_2255_, 1);
v_a_2231_ = v_b_2222_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_b_2222_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec_ref_known(v___x_2254_, 1);
v___x_2264_ = l_Lean_Syntax_getArg(v_a_2238_, v___x_2249_);
v___x_2265_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2264_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2222_, v_a_2266_);
v_a_2231_ = v___x_2267_;
goto v___jp_2230_;
}
else
{
lean_dec_ref(v_b_2222_);
return v___x_2265_;
}
}
}
}
}
v___jp_2230_:
{
size_t v___x_2232_; size_t v___x_2233_; 
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_i_2221_, v___x_2232_);
v_i_2221_ = v___x_2233_;
v_b_2222_ = v_a_2231_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2329_ = l_Lean_NameSet_empty;
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = 0;
v___x_2332_ = 1;
v___x_2333_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2333_, 0, v___x_2330_);
lean_ctor_set(v___x_2333_, 1, v___x_2329_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2, v___x_2332_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2 + 1, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2 + 2, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2 + 3, v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___y_2343_; lean_object* v_bodyInfo_2344_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2388_; lean_object* v_bodyInfo_2389_; lean_object* v___x_2392_; lean_object* v_env_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = lean_st_ref_get(v_a_2340_);
v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc_ref(v_env_2393_);
lean_dec(v___x_2392_);
lean_inc(v_stx_2334_);
v___x_2394_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2394_, 0, v_env_2393_);
lean_closure_set(v___x_2394_, 1, v_stx_2334_);
v___x_2395_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2394_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_5106_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_5106_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_5106_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
if (lean_obj_tag(v_a_2396_) == 1)
{
lean_object* v_val_2408_; lean_object* v_snd_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_del_object(v___x_2398_);
lean_dec(v_stx_2334_);
v_val_2408_ = lean_ctor_get(v_a_2396_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v_a_2396_, 1);
v_snd_2409_ = lean_ctor_get(v_val_2408_, 1);
lean_inc(v_snd_2409_);
lean_dec(v_val_2408_);
v___x_2410_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2410_, 0, lean_box(0));
lean_closure_set(v___x_2410_, 1, v_snd_2409_);
v___x_2411_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2410_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_stx_2334_ = v_a_2412_;
goto _start;
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_a_2414_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2411_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2411_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; 
lean_dec(v_a_2396_);
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
lean_inc(v_stx_2334_);
v___x_2423_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2422_);
v___x_2424_ = 1;
if (v___x_2423_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3));
lean_inc(v_stx_2334_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5));
lean_inc(v_stx_2334_);
v___x_2428_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7));
lean_inc(v_stx_2334_);
v___x_2430_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; 
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9));
lean_inc(v_stx_2334_);
v___x_2432_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2334_);
v___x_2548_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2334_);
v___x_2601_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; 
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2334_);
v___x_2603_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2661_; uint8_t v___x_2662_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; 
lean_del_object(v___x_2398_);
v___x_2661_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2334_);
v___x_2662_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2334_);
v___x_2731_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2334_);
v___x_2733_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2334_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2334_);
v___x_2737_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2334_);
v___x_2739_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2334_);
v___x_2741_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2334_);
v___x_2743_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2749_; uint8_t v___y_2750_; 
v___x_2744_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2334_);
v___x_2745_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2334_);
v___x_2754_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2334_);
v___x_2756_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2334_);
v___x_2758_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2334_);
v___x_2760_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2334_);
v___x_2762_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2334_);
v___x_2764_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2334_);
v___x_2766_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2334_);
v___x_2768_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2334_);
v___x_2770_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2334_);
v___x_2772_ = l_Lean_Syntax_isOfKind(v_stx_2334_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_env_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2773_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2774_ = lean_st_ref_get(v_a_2340_);
v_env_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_ref(v_env_2775_);
lean_dec(v___x_2774_);
v___x_2776_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2777_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2776_, v_env_2775_, v___x_2773_);
v___x_2778_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2779_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2777_, v___x_2778_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_2777_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2810_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2810_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2810_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_fst_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2808_; 
v_fst_2784_ = lean_ctor_get(v_a_2780_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_a_2780_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v_a_2780_, 1);
lean_dec(v_unused_2809_);
v___x_2786_ = v_a_2780_;
v_isShared_2787_ = v_isSharedCheck_2808_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_fst_2784_);
lean_dec(v_a_2780_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2808_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
if (lean_obj_tag(v_fst_2784_) == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_del_object(v___x_2782_);
v___x_2788_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2789_ = l_Lean_MessageData_ofName(v___x_2773_);
lean_inc_ref(v___x_2789_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 7);
lean_ctor_set(v___x_2786_, 1, v___x_2789_);
lean_ctor_set(v___x_2786_, 0, v___x_2788_);
v___x_2791_ = v___x_2786_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2792_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2795_ = l_Lean_indentD(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2793_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2789_);
v___x_2800_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2801_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2802_;
}
}
else
{
lean_object* v_val_2804_; lean_object* v___x_2806_; 
lean_del_object(v___x_2786_);
lean_dec(v___x_2773_);
lean_dec(v_stx_2334_);
v_val_2804_ = lean_ctor_get(v_fst_2784_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v_fst_2784_, 1);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_val_2804_);
v___x_2806_ = v___x_2782_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_val_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v___x_2773_);
lean_dec(v_stx_2334_);
v_a_2811_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2779_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2779_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___y_2823_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_unsigned_to_nat(5u);
v___x_2821_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2820_);
v___x_2832_ = lean_unsigned_to_nat(6u);
v___x_2833_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2832_);
lean_dec(v_stx_2334_);
v___x_2834_ = l_Lean_Syntax_getOptional_x3f(v___x_2833_);
lean_dec(v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_box(0);
v___y_2823_ = v___x_2835_;
goto v___jp_2822_;
}
else
{
lean_object* v_val_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_val_2836_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2834_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_val_2836_);
lean_dec(v___x_2834_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_val_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2823_ = v___x_2841_;
goto v___jp_2822_;
}
}
}
v___jp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2821_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2824_) == 0)
{
if (lean_obj_tag(v___y_2823_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = l_Lean_NameSet_empty;
v___x_2827_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2827_, 0, v___x_2819_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*2, v___x_2770_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*2 + 1, v___x_2770_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*2 + 2, v___x_2770_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*2 + 3, v___x_2770_);
v___y_2343_ = v_a_2825_;
v_bodyInfo_2344_ = v___x_2827_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2828_; lean_object* v_val_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2824_, 1);
v_val_2829_ = lean_ctor_get(v___y_2823_, 0);
lean_inc(v_val_2829_);
lean_dec_ref_known(v___y_2823_, 1);
v___x_2830_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2829_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___y_2343_ = v_a_2828_;
v_bodyInfo_2344_ = v_a_2831_;
goto v___jp_2342_;
}
else
{
lean_dec(v_a_2828_);
return v___x_2830_;
}
}
}
else
{
lean_dec(v___y_2823_);
return v___x_2824_;
}
}
}
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___y_2848_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_unsigned_to_nat(5u);
v___x_2846_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2845_);
v___x_2857_ = lean_unsigned_to_nat(6u);
v___x_2858_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2857_);
lean_dec(v_stx_2334_);
v___x_2859_ = l_Lean_Syntax_getOptional_x3f(v___x_2858_);
lean_dec(v___x_2858_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_box(0);
v___y_2848_ = v___x_2860_;
goto v___jp_2847_;
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v_val_2861_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2859_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_val_2861_);
lean_dec(v___x_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_val_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
v___y_2848_ = v___x_2866_;
goto v___jp_2847_;
}
}
}
v___jp_2847_:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2846_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2849_) == 0)
{
if (lean_obj_tag(v___y_2848_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l_Lean_NameSet_empty;
v___x_2852_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2852_, 0, v___x_2844_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*2, v___x_2768_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*2 + 1, v___x_2768_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*2 + 2, v___x_2768_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*2 + 3, v___x_2768_);
v___y_2388_ = v_a_2850_;
v_bodyInfo_2389_ = v___x_2852_;
goto v___jp_2387_;
}
else
{
lean_object* v_a_2853_; lean_object* v_val_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2849_, 1);
v_val_2854_ = lean_ctor_get(v___y_2848_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___y_2848_, 1);
v___x_2855_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2854_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___y_2388_ = v_a_2853_;
v_bodyInfo_2389_ = v_a_2856_;
goto v___jp_2387_;
}
else
{
lean_dec(v_a_2853_);
return v___x_2855_;
}
}
}
else
{
lean_dec(v___y_2848_);
return v___x_2849_;
}
}
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_3084_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2870_);
v___x_3085_ = l_Lean_Syntax_isNone(v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = lean_unsigned_to_nat(5u);
v___x_3087_ = l_Lean_Syntax_matchesNull(v___x_3084_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3088_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3089_ = lean_st_ref_get(v_a_2340_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_env_3090_);
lean_dec(v___x_3089_);
v___x_3091_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3092_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3091_, v_env_3090_, v___x_3088_);
v___x_3093_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3094_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3092_, v___x_3093_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3092_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3125_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3125_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3125_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_fst_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3123_; 
v_fst_3099_ = lean_ctor_get(v_a_3095_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_3095_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v_a_3095_, 1);
lean_dec(v_unused_3124_);
v___x_3101_ = v_a_3095_;
v_isShared_3102_ = v_isSharedCheck_3123_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_fst_3099_);
lean_dec(v_a_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3123_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
if (lean_obj_tag(v_fst_3099_) == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_del_object(v___x_3097_);
v___x_3103_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3104_ = l_Lean_MessageData_ofName(v___x_3088_);
lean_inc_ref(v___x_3104_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 7);
lean_ctor_set(v___x_3101_, 1, v___x_3104_);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3106_ = v___x_3101_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3107_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3110_ = l_Lean_indentD(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3108_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3104_);
v___x_3115_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3116_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3117_;
}
}
else
{
lean_object* v_val_3119_; lean_object* v___x_3121_; 
lean_del_object(v___x_3101_);
lean_dec(v___x_3088_);
lean_dec(v_stx_2334_);
v_val_3119_ = lean_ctor_get(v_fst_3099_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_fst_3099_, 1);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v_val_3119_);
v___x_3121_ = v___x_3097_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_val_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v___x_3088_);
lean_dec(v_stx_2334_);
v_a_3126_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3094_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3094_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
v___y_2872_ = v_a_2335_;
v___y_2873_ = v_a_2336_;
v___y_2874_ = v_a_2337_;
v___y_2875_ = v_a_2338_;
v___y_2876_ = v_a_2339_;
v___y_2877_ = v_a_2340_;
goto v___jp_2871_;
}
}
else
{
lean_dec(v___x_3084_);
v___y_2872_ = v_a_2335_;
v___y_2873_ = v_a_2336_;
v___y_2874_ = v_a_2337_;
v___y_2875_ = v_a_2338_;
v___y_2876_ = v_a_2339_;
v___y_2877_ = v_a_2340_;
goto v___jp_2871_;
}
v___jp_2871_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2878_ = lean_unsigned_to_nat(4u);
v___x_2879_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2878_);
v___x_2880_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2879_);
v___x_2881_ = l_Lean_Syntax_isOfKind(v___x_2879_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v_env_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v___x_2879_);
lean_inc_n(v_stx_2334_, 2);
v___x_2882_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2883_ = lean_st_ref_get(v___y_2877_);
v_env_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_ref(v_env_2884_);
lean_dec(v___x_2883_);
v___x_2885_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2886_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2885_, v_env_2884_, v___x_2882_);
v___x_2887_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2888_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2886_, v___x_2887_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___x_2886_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2919_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2919_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2919_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_fst_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2917_; 
v_fst_2893_ = lean_ctor_get(v_a_2889_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2889_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v_a_2889_, 1);
lean_dec(v_unused_2918_);
v___x_2895_ = v_a_2889_;
v_isShared_2896_ = v_isSharedCheck_2917_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_fst_2893_);
lean_dec(v_a_2889_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2917_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
if (lean_obj_tag(v_fst_2893_) == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_del_object(v___x_2891_);
v___x_2897_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2898_ = l_Lean_MessageData_ofName(v___x_2882_);
lean_inc_ref(v___x_2898_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 7);
lean_ctor_set(v___x_2895_, 1, v___x_2898_);
lean_ctor_set(v___x_2895_, 0, v___x_2897_);
v___x_2900_ = v___x_2895_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2901_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2904_ = l_Lean_indentD(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2902_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___x_2898_);
v___x_2909_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2910_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_2911_;
}
}
else
{
lean_object* v_val_2913_; lean_object* v___x_2915_; 
lean_del_object(v___x_2895_);
lean_dec(v___x_2882_);
lean_dec(v_stx_2334_);
v_val_2913_ = lean_ctor_get(v_fst_2893_, 0);
lean_inc(v_val_2913_);
lean_dec_ref_known(v_fst_2893_, 1);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v_val_2913_);
v___x_2915_ = v___x_2891_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_val_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v___x_2882_);
lean_dec(v_stx_2334_);
v_a_2920_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2888_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2888_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; size_t v_sz_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2928_ = l_Lean_Syntax_getArg(v___x_2879_, v___x_2869_);
v___x_2929_ = l_Lean_Syntax_getArgs(v___x_2928_);
lean_dec(v___x_2928_);
v_sz_2930_ = lean_array_size(v___x_2929_);
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_2766_, v_sz_2930_, v___x_2931_, v___x_2929_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_env_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec(v___x_2879_);
lean_inc_n(v_stx_2334_, 2);
v___x_2933_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2934_ = lean_st_ref_get(v___y_2877_);
v_env_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_ref(v_env_2935_);
lean_dec(v___x_2934_);
v___x_2936_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2937_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2936_, v_env_2935_, v___x_2933_);
v___x_2938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2939_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2937_, v___x_2938_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___x_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2970_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2970_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2970_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v_fst_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2968_; 
v_fst_2944_ = lean_ctor_get(v_a_2940_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v_a_2940_, 1);
lean_dec(v_unused_2969_);
v___x_2946_ = v_a_2940_;
v_isShared_2947_ = v_isSharedCheck_2968_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_fst_2944_);
lean_dec(v_a_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2968_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
if (lean_obj_tag(v_fst_2944_) == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
lean_del_object(v___x_2942_);
v___x_2948_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2949_ = l_Lean_MessageData_ofName(v___x_2933_);
lean_inc_ref(v___x_2949_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 7);
lean_ctor_set(v___x_2946_, 1, v___x_2949_);
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2951_ = v___x_2946_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2952_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2955_ = l_Lean_indentD(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2953_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2949_);
v___x_2960_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2961_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_2962_;
}
}
else
{
lean_object* v_val_2964_; lean_object* v___x_2966_; 
lean_del_object(v___x_2946_);
lean_dec(v___x_2933_);
lean_dec(v_stx_2334_);
v_val_2964_ = lean_ctor_get(v_fst_2944_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v_fst_2944_, 1);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v_val_2964_);
v___x_2966_ = v___x_2942_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_val_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v___x_2933_);
lean_dec(v_stx_2334_);
v_a_2971_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2939_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2939_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v_val_2979_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2980_ = l_Lean_Syntax_getArg(v___x_2879_, v___x_2870_);
lean_dec(v___x_2879_);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_2980_);
v___x_2982_ = l_Lean_Syntax_isOfKind(v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v_env_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec(v___x_2980_);
lean_dec(v_val_2979_);
lean_inc_n(v_stx_2334_, 2);
v___x_2983_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2984_ = lean_st_ref_get(v___y_2877_);
v_env_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc_ref(v_env_2985_);
lean_dec(v___x_2984_);
v___x_2986_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2987_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2986_, v_env_2985_, v___x_2983_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2989_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2987_, v___x_2988_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___x_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3020_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3020_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_fst_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3018_; 
v_fst_2994_ = lean_ctor_get(v_a_2990_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_a_2990_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_a_2990_, 1);
lean_dec(v_unused_3019_);
v___x_2996_ = v_a_2990_;
v_isShared_2997_ = v_isSharedCheck_3018_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_fst_2994_);
lean_dec(v_a_2990_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3018_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
if (lean_obj_tag(v_fst_2994_) == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_del_object(v___x_2992_);
v___x_2998_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2999_ = l_Lean_MessageData_ofName(v___x_2983_);
lean_inc_ref(v___x_2999_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 7);
lean_ctor_set(v___x_2996_, 1, v___x_2999_);
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3005_ = l_Lean_indentD(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3003_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___x_2999_);
v___x_3010_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3011_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_3012_;
}
}
else
{
lean_object* v_val_3014_; lean_object* v___x_3016_; 
lean_del_object(v___x_2996_);
lean_dec(v___x_2983_);
lean_dec(v_stx_2334_);
v_val_3014_ = lean_ctor_get(v_fst_2994_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v_fst_2994_, 1);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_val_3014_);
v___x_3016_ = v___x_2992_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_val_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v___x_2983_);
lean_dec(v_stx_2334_);
v_a_3021_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2989_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2989_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = l_Lean_Syntax_getArg(v___x_2980_, v___x_2870_);
v___x_3030_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3031_ = l_Lean_Syntax_isOfKind(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_env_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v___x_2980_);
lean_dec(v_val_2979_);
lean_inc_n(v_stx_2334_, 2);
v___x_3032_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3033_ = lean_st_ref_get(v___y_2877_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3036_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3035_, v_env_3034_, v___x_3032_);
v___x_3037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3038_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3036_, v___x_3037_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___x_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3069_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3069_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3069_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_fst_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3067_; 
v_fst_3043_ = lean_ctor_get(v_a_3039_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_a_3039_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; 
v_unused_3068_ = lean_ctor_get(v_a_3039_, 1);
lean_dec(v_unused_3068_);
v___x_3045_ = v_a_3039_;
v_isShared_3046_ = v_isSharedCheck_3067_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_fst_3043_);
lean_dec(v_a_3039_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3067_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
if (lean_obj_tag(v_fst_3043_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_del_object(v___x_3041_);
v___x_3047_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3048_ = l_Lean_MessageData_ofName(v___x_3032_);
lean_inc_ref(v___x_3048_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 7);
lean_ctor_set(v___x_3045_, 1, v___x_3048_);
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3050_ = v___x_3045_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3051_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3054_ = l_Lean_indentD(v___x_3053_);
v___x_3055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3052_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v___x_3048_);
v___x_3059_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3060_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_3061_;
}
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3065_; 
lean_del_object(v___x_3045_);
lean_dec(v___x_3032_);
lean_dec(v_stx_2334_);
v_val_3063_ = lean_ctor_get(v_fst_3043_, 0);
lean_inc(v_val_3063_);
lean_dec_ref_known(v_fst_3043_, 1);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v_val_3063_);
v___x_3065_ = v___x_3041_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_val_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___x_3032_);
lean_dec(v_stx_2334_);
v_a_3070_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3038_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3038_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v_stx_2334_);
v___x_3078_ = lean_unsigned_to_nat(3u);
v___x_3079_ = l_Lean_Syntax_getArg(v___x_2980_, v___x_3078_);
lean_dec(v___x_2980_);
v___x_3080_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3079_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; size_t v_sz_3082_; lean_object* v___x_3083_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v_sz_3082_ = lean_array_size(v_val_2979_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2979_, v_sz_3082_, v___x_2931_, v_a_3081_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v_val_2979_);
return v___x_3083_;
}
else
{
lean_dec(v_val_2979_);
return v___x_3080_;
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
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v_stx_2334_);
v___x_3134_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_stx_2334_);
v___x_3136_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec(v_stx_2334_);
v___x_3138_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec(v_stx_2334_);
v___x_3140_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_stx_2334_);
v___x_3142_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
}
else
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; size_t v_sz_3147_; size_t v___x_3148_; lean_object* v___x_3149_; 
v___x_3144_ = lean_unsigned_to_nat(2u);
v___x_3145_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3144_);
v___x_3146_ = l_Lean_Syntax_getArgs(v___x_3145_);
lean_dec(v___x_3145_);
v_sz_3147_ = lean_array_size(v___x_3146_);
v___x_3148_ = ((size_t)0ULL);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3147_, v___x_3148_, v___x_3146_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_env_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3150_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3151_ = lean_st_ref_get(v_a_2340_);
v_env_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_ref(v_env_3152_);
lean_dec(v___x_3151_);
v___x_3153_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3154_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3153_, v_env_3152_, v___x_3150_);
v___x_3155_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3156_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3154_, v___x_3155_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3154_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3187_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3187_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3187_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v_fst_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3185_; 
v_fst_3161_ = lean_ctor_get(v_a_3157_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_a_3157_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; 
v_unused_3186_ = lean_ctor_get(v_a_3157_, 1);
lean_dec(v_unused_3186_);
v___x_3163_ = v_a_3157_;
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_fst_3161_);
lean_dec(v_a_3157_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_fst_3161_) == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_del_object(v___x_3159_);
v___x_3165_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3166_ = l_Lean_MessageData_ofName(v___x_3150_);
lean_inc_ref(v___x_3166_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 7);
lean_ctor_set(v___x_3163_, 1, v___x_3166_);
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3169_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3172_ = l_Lean_indentD(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3170_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3166_);
v___x_3177_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3178_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3179_;
}
}
else
{
lean_object* v_val_3181_; lean_object* v___x_3183_; 
lean_del_object(v___x_3163_);
lean_dec(v___x_3150_);
lean_dec(v_stx_2334_);
v_val_3181_ = lean_ctor_get(v_fst_3161_, 0);
lean_inc(v_val_3181_);
lean_dec_ref_known(v_fst_3161_, 1);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v_val_3181_);
v___x_3183_ = v___x_3159_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_val_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v___x_3150_);
lean_dec(v_stx_2334_);
v_a_3188_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3156_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3156_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_val_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3330_; 
v_val_3196_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3198_ = v___x_3149_;
v_isShared_3199_ = v_isSharedCheck_3330_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_val_3196_);
lean_dec(v___x_3149_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3330_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_finSeq_x3f_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3200_ = lean_unsigned_to_nat(1u);
v___x_3201_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3200_);
v___x_3225_ = lean_unsigned_to_nat(3u);
v___x_3226_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3225_);
v___x_3227_ = l_Lean_Syntax_isNone(v___x_3226_);
if (v___x_3227_ == 0)
{
uint8_t v___x_3228_; 
lean_inc(v___x_3226_);
v___x_3228_ = l_Lean_Syntax_matchesNull(v___x_3226_, v___x_3200_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v_env_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_dec(v___x_3226_);
lean_dec(v___x_3201_);
lean_del_object(v___x_3198_);
lean_dec(v_val_3196_);
lean_inc_n(v_stx_2334_, 2);
v___x_3229_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3230_ = lean_st_ref_get(v_a_2340_);
v_env_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_ref(v_env_3231_);
lean_dec(v___x_3230_);
v___x_3232_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3233_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3232_, v_env_3231_, v___x_3229_);
v___x_3234_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3235_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3233_, v___x_3234_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3233_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3266_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v_fst_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3264_; 
v_fst_3240_ = lean_ctor_get(v_a_3236_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3236_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_a_3236_, 1);
lean_dec(v_unused_3265_);
v___x_3242_ = v_a_3236_;
v_isShared_3243_ = v_isSharedCheck_3264_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_fst_3240_);
lean_dec(v_a_3236_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3264_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
if (lean_obj_tag(v_fst_3240_) == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_del_object(v___x_3238_);
v___x_3244_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3245_ = l_Lean_MessageData_ofName(v___x_3229_);
lean_inc_ref(v___x_3245_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 7);
lean_ctor_set(v___x_3242_, 1, v___x_3245_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3247_ = v___x_3242_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3248_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3251_ = l_Lean_indentD(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3249_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3245_);
v___x_3256_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3257_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3258_;
}
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; 
lean_del_object(v___x_3242_);
lean_dec(v___x_3229_);
lean_dec(v_stx_2334_);
v_val_3260_ = lean_ctor_get(v_fst_3240_, 0);
lean_inc(v_val_3260_);
lean_dec_ref_known(v_fst_3240_, 1);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v_val_3260_);
v___x_3262_ = v___x_3238_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_val_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v___x_3229_);
lean_dec(v_stx_2334_);
v_a_3267_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3235_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3235_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3275_ = lean_unsigned_to_nat(0u);
v___x_3276_ = l_Lean_Syntax_getArg(v___x_3226_, v___x_3275_);
lean_dec(v___x_3226_);
v___x_3277_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3276_);
v___x_3278_ = l_Lean_Syntax_isOfKind(v___x_3276_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_env_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v___x_3276_);
lean_dec(v___x_3201_);
lean_del_object(v___x_3198_);
lean_dec(v_val_3196_);
lean_inc_n(v_stx_2334_, 2);
v___x_3279_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3280_ = lean_st_ref_get(v_a_2340_);
v_env_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc_ref(v_env_3281_);
lean_dec(v___x_3280_);
v___x_3282_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3283_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3282_, v_env_3281_, v___x_3279_);
v___x_3284_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3285_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3283_, v___x_3284_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3283_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3316_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3316_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3316_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_fst_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3314_; 
v_fst_3290_ = lean_ctor_get(v_a_3286_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_a_3286_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; 
v_unused_3315_ = lean_ctor_get(v_a_3286_, 1);
lean_dec(v_unused_3315_);
v___x_3292_ = v_a_3286_;
v_isShared_3293_ = v_isSharedCheck_3314_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_fst_3290_);
lean_dec(v_a_3286_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3314_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
if (lean_obj_tag(v_fst_3290_) == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_del_object(v___x_3288_);
v___x_3294_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3295_ = l_Lean_MessageData_ofName(v___x_3279_);
lean_inc_ref(v___x_3295_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 7);
lean_ctor_set(v___x_3292_, 1, v___x_3295_);
lean_ctor_set(v___x_3292_, 0, v___x_3294_);
v___x_3297_ = v___x_3292_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3298_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3301_ = l_Lean_indentD(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3299_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3295_);
v___x_3306_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3307_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3308_;
}
}
else
{
lean_object* v_val_3310_; lean_object* v___x_3312_; 
lean_del_object(v___x_3292_);
lean_dec(v___x_3279_);
lean_dec(v_stx_2334_);
v_val_3310_ = lean_ctor_get(v_fst_3290_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v_fst_3290_, 1);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_val_3310_);
v___x_3312_ = v___x_3288_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_val_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___x_3279_);
lean_dec(v_stx_2334_);
v_a_3317_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3285_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3285_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
lean_dec(v_stx_2334_);
v___x_3325_ = l_Lean_Syntax_getArg(v___x_3276_, v___x_3200_);
lean_dec(v___x_3276_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3325_);
v___x_3327_ = v___x_3198_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
v_finSeq_x3f_3203_ = v___x_3327_;
v___y_3204_ = v_a_2335_;
v___y_3205_ = v_a_2336_;
v___y_3206_ = v_a_2337_;
v___y_3207_ = v_a_2338_;
v___y_3208_ = v_a_2339_;
v___y_3209_ = v_a_2340_;
goto v___jp_3202_;
}
}
}
}
else
{
lean_object* v___x_3329_; 
lean_dec(v___x_3226_);
lean_del_object(v___x_3198_);
lean_dec(v_stx_2334_);
v___x_3329_ = lean_box(0);
v_finSeq_x3f_3203_ = v___x_3329_;
v___y_3204_ = v_a_2335_;
v___y_3205_ = v_a_2336_;
v___y_3206_ = v_a_2337_;
v___y_3207_ = v_a_2338_;
v___y_3208_ = v_a_2339_;
v___y_3209_ = v_a_2340_;
goto v___jp_3202_;
}
v___jp_3202_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3201_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; size_t v_sz_3212_; lean_object* v___x_3213_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_sz_3212_ = lean_array_size(v_val_3196_);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3196_, v_sz_3212_, v___x_3148_, v_a_3211_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v_val_3196_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3224_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3218_ = v___x_3215_;
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3215_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3214_, v_a_3216_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
else
{
lean_dec(v_a_3214_);
return v___x_3215_;
}
}
else
{
lean_dec(v_finSeq_x3f_3203_);
return v___x_3213_;
}
}
else
{
lean_dec(v_finSeq_x3f_3203_);
lean_dec(v_val_3196_);
return v___x_3210_;
}
}
}
}
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_unsigned_to_nat(1u);
v___x_3455_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3332_);
v___x_3456_ = l_Lean_Syntax_isNone(v___x_3455_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
lean_inc(v___x_3455_);
v___x_3457_ = l_Lean_Syntax_matchesNull(v___x_3455_, v___x_3332_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_env_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec(v___x_3455_);
lean_inc_n(v_stx_2334_, 2);
v___x_3458_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3459_ = lean_st_ref_get(v_a_2340_);
v_env_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc_ref(v_env_3460_);
lean_dec(v___x_3459_);
v___x_3461_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3462_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3461_, v_env_3460_, v___x_3458_);
v___x_3463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3464_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3462_, v___x_3463_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3462_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3495_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3495_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3495_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_fst_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3493_; 
v_fst_3469_ = lean_ctor_get(v_a_3465_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v_a_3465_, 1);
lean_dec(v_unused_3494_);
v___x_3471_ = v_a_3465_;
v_isShared_3472_ = v_isSharedCheck_3493_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_fst_3469_);
lean_dec(v_a_3465_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3493_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_fst_3469_) == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
lean_del_object(v___x_3467_);
v___x_3473_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3474_ = l_Lean_MessageData_ofName(v___x_3458_);
lean_inc_ref(v___x_3474_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 7);
lean_ctor_set(v___x_3471_, 1, v___x_3474_);
lean_ctor_set(v___x_3471_, 0, v___x_3473_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3477_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3480_ = l_Lean_indentD(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3478_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___x_3474_);
v___x_3485_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3486_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3487_;
}
}
else
{
lean_object* v_val_3489_; lean_object* v___x_3491_; 
lean_del_object(v___x_3471_);
lean_dec(v___x_3458_);
lean_dec(v_stx_2334_);
v_val_3489_ = lean_ctor_get(v_fst_3469_, 0);
lean_inc(v_val_3489_);
lean_dec_ref_known(v_fst_3469_, 1);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_val_3489_);
v___x_3491_ = v___x_3467_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_val_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v___x_3458_);
lean_dec(v_stx_2334_);
v_a_3496_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3464_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3464_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
if (v___x_3456_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3504_ = l_Lean_Syntax_getArg(v___x_3455_, v___x_3331_);
lean_dec(v___x_3455_);
v___x_3505_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3506_ = l_Lean_Syntax_isOfKind(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v_env_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3507_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3508_ = lean_st_ref_get(v_a_2340_);
v_env_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc_ref(v_env_3509_);
lean_dec(v___x_3508_);
v___x_3510_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3511_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3510_, v_env_3509_, v___x_3507_);
v___x_3512_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3513_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3511_, v___x_3512_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3544_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3544_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3544_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_fst_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3542_; 
v_fst_3518_ = lean_ctor_get(v_a_3514_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v_a_3514_, 1);
lean_dec(v_unused_3543_);
v___x_3520_ = v_a_3514_;
v_isShared_3521_ = v_isSharedCheck_3542_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_fst_3518_);
lean_dec(v_a_3514_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3542_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
if (lean_obj_tag(v_fst_3518_) == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
lean_del_object(v___x_3516_);
v___x_3522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3523_ = l_Lean_MessageData_ofName(v___x_3507_);
lean_inc_ref(v___x_3523_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set_tag(v___x_3520_, 7);
lean_ctor_set(v___x_3520_, 1, v___x_3523_);
lean_ctor_set(v___x_3520_, 0, v___x_3522_);
v___x_3525_ = v___x_3520_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3529_ = l_Lean_indentD(v___x_3528_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3527_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v___x_3523_);
v___x_3534_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3535_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3536_;
}
}
else
{
lean_object* v_val_3538_; lean_object* v___x_3540_; 
lean_del_object(v___x_3520_);
lean_dec(v___x_3507_);
lean_dec(v_stx_2334_);
v_val_3538_ = lean_ctor_get(v_fst_3518_, 0);
lean_inc(v_val_3538_);
lean_dec_ref_known(v_fst_3518_, 1);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v_val_3538_);
v___x_3540_ = v___x_3516_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_val_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v___x_3507_);
lean_dec(v_stx_2334_);
v_a_3545_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3513_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3513_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
v___y_3353_ = v_a_2338_;
v___y_3354_ = v_a_2339_;
v___y_3355_ = v_a_2340_;
goto v___jp_3349_;
}
}
else
{
lean_dec(v___x_3455_);
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
v___y_3353_ = v_a_2338_;
v___y_3354_ = v_a_2339_;
v___y_3355_ = v_a_2340_;
goto v___jp_3349_;
}
}
}
else
{
lean_dec(v___x_3455_);
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
v___y_3353_ = v_a_2338_;
v___y_3354_ = v_a_2339_;
v___y_3355_ = v_a_2340_;
goto v___jp_3349_;
}
v___jp_3333_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(3u);
v___x_3341_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3340_);
lean_dec(v_stx_2334_);
v___x_3342_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3341_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; uint8_t v_breaks_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v_breaks_3344_ = lean_ctor_get_uint8(v_a_3343_, sizeof(void*)*2);
if (v_breaks_3344_ == 0)
{
uint8_t v_returnsEarly_3345_; lean_object* v_reassigns_3346_; 
v_returnsEarly_3345_ = lean_ctor_get_uint8(v_a_3343_, sizeof(void*)*2 + 2);
v_reassigns_3346_ = lean_ctor_get(v_a_3343_, 1);
lean_inc(v_reassigns_3346_);
lean_dec(v_a_3343_);
v___y_2747_ = v___x_3331_;
v___y_2748_ = v_returnsEarly_3345_;
v___y_2749_ = v_reassigns_3346_;
v___y_2750_ = v___x_2754_;
goto v___jp_2746_;
}
else
{
uint8_t v_returnsEarly_3347_; lean_object* v_reassigns_3348_; 
v_returnsEarly_3347_ = lean_ctor_get_uint8(v_a_3343_, sizeof(void*)*2 + 2);
v_reassigns_3348_ = lean_ctor_get(v_a_3343_, 1);
lean_inc(v_reassigns_3348_);
lean_dec(v_a_3343_);
v___y_2747_ = v___x_3332_;
v___y_2748_ = v_returnsEarly_3347_;
v___y_2749_ = v_reassigns_3348_;
v___y_2750_ = v___x_2745_;
goto v___jp_2746_;
}
}
else
{
return v___x_3342_;
}
}
v___jp_3349_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(2u);
v___x_3357_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3356_);
v___x_3358_ = l_Lean_Syntax_isNone(v___x_3357_);
if (v___x_3358_ == 0)
{
uint8_t v___x_3359_; 
lean_inc(v___x_3357_);
v___x_3359_ = l_Lean_Syntax_matchesNull(v___x_3357_, v___x_3332_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v_env_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec(v___x_3357_);
lean_inc_n(v_stx_2334_, 2);
v___x_3360_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3361_ = lean_st_ref_get(v___y_3355_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
v___x_3363_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3364_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3363_, v_env_3362_, v___x_3360_);
v___x_3365_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3366_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3364_, v___x_3365_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___x_3364_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3397_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_fst_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3395_; 
v_fst_3371_ = lean_ctor_get(v_a_3367_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v_a_3367_, 1);
lean_dec(v_unused_3396_);
v___x_3373_ = v_a_3367_;
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_fst_3371_);
lean_dec(v_a_3367_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
if (lean_obj_tag(v_fst_3371_) == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_del_object(v___x_3369_);
v___x_3375_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3376_ = l_Lean_MessageData_ofName(v___x_3360_);
lean_inc_ref(v___x_3376_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 7);
lean_ctor_set(v___x_3373_, 1, v___x_3376_);
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3378_ = v___x_3373_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3382_ = l_Lean_indentD(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3380_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3376_);
v___x_3387_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3388_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3389_;
}
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3393_; 
lean_del_object(v___x_3373_);
lean_dec(v___x_3360_);
lean_dec(v_stx_2334_);
v_val_3391_ = lean_ctor_get(v_fst_3371_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v_fst_3371_, 1);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_val_3391_);
v___x_3393_ = v___x_3369_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_val_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v___x_3360_);
lean_dec(v_stx_2334_);
v_a_3398_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3366_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3366_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
if (v___x_3358_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = l_Lean_Syntax_getArg(v___x_3357_, v___x_3331_);
lean_dec(v___x_3357_);
v___x_3407_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3408_ = l_Lean_Syntax_isOfKind(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v_env_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3409_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3410_ = lean_st_ref_get(v___y_3355_);
v_env_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc_ref(v_env_3411_);
lean_dec(v___x_3410_);
v___x_3412_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3413_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3412_, v_env_3411_, v___x_3409_);
v___x_3414_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3415_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3413_, v___x_3414_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___x_3413_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3446_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3446_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3446_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3444_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_a_3416_, 1);
lean_dec(v_unused_3445_);
v___x_3422_ = v_a_3416_;
v_isShared_3423_ = v_isSharedCheck_3444_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3444_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
if (lean_obj_tag(v_fst_3420_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_del_object(v___x_3418_);
v___x_3424_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3425_ = l_Lean_MessageData_ofName(v___x_3409_);
lean_inc_ref(v___x_3425_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 7);
lean_ctor_set(v___x_3422_, 1, v___x_3425_);
lean_ctor_set(v___x_3422_, 0, v___x_3424_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3428_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3431_ = l_Lean_indentD(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v___x_3425_);
v___x_3436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3437_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3438_;
}
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3442_; 
lean_del_object(v___x_3422_);
lean_dec(v___x_3409_);
lean_dec(v_stx_2334_);
v_val_3440_ = lean_ctor_get(v_fst_3420_, 0);
lean_inc(v_val_3440_);
lean_dec_ref_known(v_fst_3420_, 1);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_val_3440_);
v___x_3442_ = v___x_3418_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_val_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___x_3409_);
lean_dec(v_stx_2334_);
v_a_3447_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3415_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3415_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
v___y_3337_ = v___y_3353_;
v___y_3338_ = v___y_3354_;
v___y_3339_ = v___y_3355_;
goto v___jp_3333_;
}
}
else
{
lean_dec(v___x_3357_);
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
v___y_3337_ = v___y_3353_;
v___y_3338_ = v___y_3354_;
v___y_3339_ = v___y_3355_;
goto v___jp_3333_;
}
}
}
else
{
lean_dec(v___x_3357_);
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
v___y_3337_ = v___y_3353_;
v___y_3338_ = v___y_3354_;
v___y_3339_ = v___y_3355_;
goto v___jp_3333_;
}
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3690_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3553_ = lean_unsigned_to_nat(0u);
v___x_3554_ = lean_unsigned_to_nat(1u);
v___x_3839_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3554_);
v___x_3840_ = l_Lean_Syntax_getArgs(v___x_3839_);
lean_dec(v___x_3839_);
v___x_3841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3842_ = lean_array_get_size(v___x_3840_);
v___x_3843_ = lean_nat_dec_lt(v___x_3553_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_dec_ref(v___x_3840_);
v___y_3690_ = v___x_3841_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; size_t v___x_3846_; size_t v___x_3847_; lean_object* v___x_3848_; lean_object* v_snd_3849_; 
v___x_3844_ = lean_box(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v___x_3841_);
v___x_3846_ = ((size_t)0ULL);
v___x_3847_ = lean_usize_of_nat(v___x_3842_);
v___x_3848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2745_, v___x_2743_, v___x_3840_, v___x_3846_, v___x_3847_, v___x_3845_);
lean_dec_ref(v___x_3840_);
v_snd_3849_ = lean_ctor_get(v___x_3848_, 1);
lean_inc(v_snd_3849_);
lean_dec_ref(v___x_3848_);
v___y_3690_ = v_snd_3849_;
goto v___jp_3689_;
}
v___jp_3555_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_unsigned_to_nat(5u);
v___x_3563_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3562_);
lean_dec(v_stx_2334_);
v___x_3564_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3563_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3582_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
uint8_t v_returnsEarly_3569_; lean_object* v_reassigns_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3580_; 
v_returnsEarly_3569_ = lean_ctor_get_uint8(v_a_3565_, sizeof(void*)*2 + 2);
v_reassigns_3570_ = lean_ctor_get(v_a_3565_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3565_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_a_3565_, 0);
lean_dec(v_unused_3581_);
v___x_3572_ = v_a_3565_;
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_reassigns_3570_);
lean_dec(v_a_3565_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3554_);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_reassigns_3570_);
lean_ctor_set_uint8(v_reuseFailAlloc_3579_, sizeof(void*)*2 + 2, v_returnsEarly_3569_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*2, v___x_2743_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*2 + 1, v___x_2743_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*2 + 3, v___x_2743_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3575_);
v___x_3577_ = v___x_3567_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
else
{
return v___x_3564_;
}
}
v___jp_3583_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3590_ = lean_unsigned_to_nat(3u);
v___x_3591_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3590_);
v___x_3592_ = l_Lean_Syntax_isNone(v___x_3591_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
lean_inc(v___x_3591_);
v___x_3593_ = l_Lean_Syntax_matchesNull(v___x_3591_, v___x_3554_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v_env_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec(v___x_3591_);
lean_inc_n(v_stx_2334_, 2);
v___x_3594_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3595_ = lean_st_ref_get(v___y_3589_);
v_env_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc_ref(v_env_3596_);
lean_dec(v___x_3595_);
v___x_3597_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3598_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3597_, v_env_3596_, v___x_3594_);
v___x_3599_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3600_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3598_, v___x_3599_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___x_3598_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3631_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3631_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3629_; 
v_fst_3605_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_a_3601_, 1);
lean_dec(v_unused_3630_);
v___x_3607_ = v_a_3601_;
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_fst_3605_);
lean_dec(v_a_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
if (lean_obj_tag(v_fst_3605_) == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_del_object(v___x_3603_);
v___x_3609_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3610_ = l_Lean_MessageData_ofName(v___x_3594_);
lean_inc_ref(v___x_3610_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 7);
lean_ctor_set(v___x_3607_, 1, v___x_3610_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3612_ = v___x_3607_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3613_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3616_ = l_Lean_indentD(v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3610_);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3622_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3623_;
}
}
else
{
lean_object* v_val_3625_; lean_object* v___x_3627_; 
lean_del_object(v___x_3607_);
lean_dec(v___x_3594_);
lean_dec(v_stx_2334_);
v_val_3625_ = lean_ctor_get(v_fst_3605_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v_fst_3605_, 1);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_val_3625_);
v___x_3627_ = v___x_3603_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_val_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___x_3594_);
lean_dec(v_stx_2334_);
v_a_3632_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3600_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3600_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
if (v___x_3592_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3640_ = l_Lean_Syntax_getArg(v___x_3591_, v___x_3553_);
lean_dec(v___x_3591_);
v___x_3641_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3642_ = l_Lean_Syntax_isOfKind(v___x_3640_, v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_env_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3643_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3644_ = lean_st_ref_get(v___y_3589_);
v_env_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc_ref(v_env_3645_);
lean_dec(v___x_3644_);
v___x_3646_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3647_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3646_, v_env_3645_, v___x_3643_);
v___x_3648_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3649_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3647_, v___x_3648_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___x_3647_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3680_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3680_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3680_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_fst_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3678_; 
v_fst_3654_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_a_3650_, 1);
lean_dec(v_unused_3679_);
v___x_3656_ = v_a_3650_;
v_isShared_3657_ = v_isSharedCheck_3678_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_fst_3654_);
lean_dec(v_a_3650_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3678_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_del_object(v___x_3652_);
v___x_3658_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3659_ = l_Lean_MessageData_ofName(v___x_3643_);
lean_inc_ref(v___x_3659_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 7);
lean_ctor_set(v___x_3656_, 1, v___x_3659_);
lean_ctor_set(v___x_3656_, 0, v___x_3658_);
v___x_3661_ = v___x_3656_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3662_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3665_ = l_Lean_indentD(v___x_3664_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3663_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v___x_3659_);
v___x_3670_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3669_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3671_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3672_;
}
}
else
{
lean_object* v_val_3674_; lean_object* v___x_3676_; 
lean_del_object(v___x_3656_);
lean_dec(v___x_3643_);
lean_dec(v_stx_2334_);
v_val_3674_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3674_);
lean_dec_ref_known(v_fst_3654_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3674_);
v___x_3676_ = v___x_3652_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_val_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v___x_3643_);
lean_dec(v_stx_2334_);
v_a_3681_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3649_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3649_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
v___y_3559_ = v___y_3587_;
v___y_3560_ = v___y_3588_;
v___y_3561_ = v___y_3589_;
goto v___jp_3555_;
}
}
else
{
lean_dec(v___x_3591_);
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
v___y_3559_ = v___y_3587_;
v___y_3560_ = v___y_3588_;
v___y_3561_ = v___y_3589_;
goto v___jp_3555_;
}
}
}
else
{
lean_dec(v___x_3591_);
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
v___y_3559_ = v___y_3587_;
v___y_3560_ = v___y_3588_;
v___y_3561_ = v___y_3589_;
goto v___jp_3555_;
}
}
v___jp_3689_:
{
size_t v_sz_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v_sz_3691_ = lean_array_size(v___y_3690_);
v___x_3692_ = ((size_t)0ULL);
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3691_, v___x_3692_, v___y_3690_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_env_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3694_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3695_ = lean_st_ref_get(v_a_2340_);
v_env_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc_ref(v_env_3696_);
lean_dec(v___x_3695_);
v___x_3697_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3698_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3697_, v_env_3696_, v___x_3694_);
v___x_3699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3700_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3698_, v___x_3699_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3698_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3731_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_fst_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3729_; 
v_fst_3705_ = lean_ctor_get(v_a_3701_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_a_3701_, 1);
lean_dec(v_unused_3730_);
v___x_3707_ = v_a_3701_;
v_isShared_3708_ = v_isSharedCheck_3729_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_fst_3705_);
lean_dec(v_a_3701_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3729_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
if (lean_obj_tag(v_fst_3705_) == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_del_object(v___x_3703_);
v___x_3709_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3710_ = l_Lean_MessageData_ofName(v___x_3694_);
lean_inc_ref(v___x_3710_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set_tag(v___x_3707_, 7);
lean_ctor_set(v___x_3707_, 1, v___x_3710_);
lean_ctor_set(v___x_3707_, 0, v___x_3709_);
v___x_3712_ = v___x_3707_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3713_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3716_ = l_Lean_indentD(v___x_3715_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3714_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3710_);
v___x_3721_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3722_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3723_;
}
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; 
lean_del_object(v___x_3707_);
lean_dec(v___x_3694_);
lean_dec(v_stx_2334_);
v_val_3725_ = lean_ctor_get(v_fst_3705_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v_fst_3705_, 1);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_val_3725_);
v___x_3727_ = v___x_3703_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_val_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v___x_3694_);
lean_dec(v_stx_2334_);
v_a_3732_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3700_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3700_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; 
lean_dec_ref_known(v___x_3693_, 1);
v___x_3740_ = lean_unsigned_to_nat(2u);
v___x_3741_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_isNone(v___x_3741_);
if (v___x_3742_ == 0)
{
uint8_t v___x_3743_; 
lean_inc(v___x_3741_);
v___x_3743_ = l_Lean_Syntax_matchesNull(v___x_3741_, v___x_3554_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_env_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v___x_3741_);
lean_inc_n(v_stx_2334_, 2);
v___x_3744_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3745_ = lean_st_ref_get(v_a_2340_);
v_env_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc_ref(v_env_3746_);
lean_dec(v___x_3745_);
v___x_3747_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3748_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3747_, v_env_3746_, v___x_3744_);
v___x_3749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3750_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3748_, v___x_3749_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3748_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3781_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_fst_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3779_; 
v_fst_3755_ = lean_ctor_get(v_a_3751_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v_a_3751_, 1);
lean_dec(v_unused_3780_);
v___x_3757_ = v_a_3751_;
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_fst_3755_);
lean_dec(v_a_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3779_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
if (lean_obj_tag(v_fst_3755_) == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_del_object(v___x_3753_);
v___x_3759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3760_ = l_Lean_MessageData_ofName(v___x_3744_);
lean_inc_ref(v___x_3760_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 7);
lean_ctor_set(v___x_3757_, 1, v___x_3760_);
lean_ctor_set(v___x_3757_, 0, v___x_3759_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3763_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3766_ = l_Lean_indentD(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3760_);
v___x_3771_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3772_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3773_;
}
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3777_; 
lean_del_object(v___x_3757_);
lean_dec(v___x_3744_);
lean_dec(v_stx_2334_);
v_val_3775_ = lean_ctor_get(v_fst_3755_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_fst_3755_, 1);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v_val_3775_);
v___x_3777_ = v___x_3753_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_val_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v___x_3744_);
lean_dec(v_stx_2334_);
v_a_3782_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3750_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3750_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
if (v___x_3742_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = l_Lean_Syntax_getArg(v___x_3741_, v___x_3553_);
lean_dec(v___x_3741_);
v___x_3791_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3792_ = l_Lean_Syntax_isOfKind(v___x_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v_env_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3793_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3794_ = lean_st_ref_get(v_a_2340_);
v_env_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc_ref(v_env_3795_);
lean_dec(v___x_3794_);
v___x_3796_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3797_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3796_, v_env_3795_, v___x_3793_);
v___x_3798_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3799_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3797_, v___x_3798_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3797_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3830_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3830_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3830_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_fst_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3828_; 
v_fst_3804_ = lean_ctor_get(v_a_3800_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v_a_3800_, 1);
lean_dec(v_unused_3829_);
v___x_3806_ = v_a_3800_;
v_isShared_3807_ = v_isSharedCheck_3828_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_fst_3804_);
lean_dec(v_a_3800_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3828_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
if (lean_obj_tag(v_fst_3804_) == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_del_object(v___x_3802_);
v___x_3808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3809_ = l_Lean_MessageData_ofName(v___x_3793_);
lean_inc_ref(v___x_3809_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 7);
lean_ctor_set(v___x_3806_, 1, v___x_3809_);
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3811_ = v___x_3806_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3815_ = l_Lean_indentD(v___x_3814_);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3813_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set(v___x_3819_, 1, v___x_3809_);
v___x_3820_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3821_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3822_;
}
}
else
{
lean_object* v_val_3824_; lean_object* v___x_3826_; 
lean_del_object(v___x_3806_);
lean_dec(v___x_3793_);
lean_dec(v_stx_2334_);
v_val_3824_ = lean_ctor_get(v_fst_3804_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_fst_3804_, 1);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_val_3824_);
v___x_3826_ = v___x_3802_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_val_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v___x_3793_);
lean_dec(v_stx_2334_);
v_a_3831_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3799_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3799_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
v___y_3587_ = v_a_2338_;
v___y_3588_ = v_a_2339_;
v___y_3589_ = v_a_2340_;
goto v___jp_3583_;
}
}
else
{
lean_dec(v___x_3741_);
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
v___y_3587_ = v_a_2338_;
v___y_3588_ = v_a_2339_;
v___y_3589_ = v_a_2340_;
goto v___jp_3583_;
}
}
}
else
{
lean_dec(v___x_3741_);
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
v___y_3587_ = v_a_2338_;
v___y_3588_ = v_a_2339_;
v___y_3589_ = v_a_2340_;
goto v___jp_3583_;
}
}
}
}
v___jp_2746_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2751_, 0, v___y_2747_);
lean_ctor_set(v___x_2751_, 1, v___y_2749_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2, v___x_2745_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 1, v___x_2745_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 2, v___y_2748_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 3, v___y_2750_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_unsigned_to_nat(3u);
v___x_3852_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3851_);
lean_dec(v_stx_2334_);
v___x_3853_ = l_Lean_NameSet_empty;
v___x_3854_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3854_, 0, v___x_3850_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*2, v___x_2741_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*2 + 1, v___x_2741_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*2 + 2, v___x_2741_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*2 + 3, v___x_2741_);
v___x_3855_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3852_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3864_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3864_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3864_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3860_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3854_, v_a_3856_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3860_);
v___x_3862_ = v___x_3858_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
else
{
lean_dec_ref_known(v___x_3854_, 2);
return v___x_3855_;
}
}
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; size_t v_sz_3868_; size_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3865_ = lean_unsigned_to_nat(4u);
v___x_3866_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3865_);
v___x_3867_ = l_Lean_Syntax_getArgs(v___x_3866_);
lean_dec(v___x_3866_);
v_sz_3868_ = lean_array_size(v___x_3867_);
v___x_3869_ = ((size_t)0ULL);
v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3868_, v___x_3869_, v___x_3867_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v_env_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc_n(v_stx_2334_, 2);
v___x_3871_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3872_ = lean_st_ref_get(v_a_2340_);
v_env_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc_ref(v_env_3873_);
lean_dec(v___x_3872_);
v___x_3874_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3875_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3874_, v_env_3873_, v___x_3871_);
v___x_3876_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3877_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3875_, v___x_3876_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3875_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3908_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3908_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3908_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_fst_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3906_; 
v_fst_3882_ = lean_ctor_get(v_a_3878_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_a_3878_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; 
v_unused_3907_ = lean_ctor_get(v_a_3878_, 1);
lean_dec(v_unused_3907_);
v___x_3884_ = v_a_3878_;
v_isShared_3885_ = v_isSharedCheck_3906_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_fst_3882_);
lean_dec(v_a_3878_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3906_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
if (lean_obj_tag(v_fst_3882_) == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
lean_del_object(v___x_3880_);
v___x_3886_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3887_ = l_Lean_MessageData_ofName(v___x_3871_);
lean_inc_ref(v___x_3887_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 7);
lean_ctor_set(v___x_3884_, 1, v___x_3887_);
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3889_ = v___x_3884_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3890_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3893_ = l_Lean_indentD(v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3891_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v___x_3887_);
v___x_3898_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3899_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3900_;
}
}
else
{
lean_object* v_val_3902_; lean_object* v___x_3904_; 
lean_del_object(v___x_3884_);
lean_dec(v___x_3871_);
lean_dec(v_stx_2334_);
v_val_3902_ = lean_ctor_get(v_fst_3882_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v_fst_3882_, 1);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v_val_3902_);
v___x_3904_ = v___x_3880_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_val_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec(v___x_3871_);
lean_dec(v_stx_2334_);
v_a_3909_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3877_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3877_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v_val_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_4004_; 
v_val_3917_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3919_ = v___x_3870_;
v_isShared_3920_ = v_isSharedCheck_4004_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_val_3917_);
lean_dec(v___x_3870_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_4004_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_elseSeq_x3f_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3921_ = lean_unsigned_to_nat(3u);
v___x_3922_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3921_);
v___x_3947_ = lean_unsigned_to_nat(5u);
v___x_3948_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_3947_);
v___x_3949_ = l_Lean_Syntax_isNone(v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3948_);
v___x_3951_ = l_Lean_Syntax_matchesNull(v___x_3948_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v_env_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_dec(v___x_3948_);
lean_dec(v___x_3922_);
lean_del_object(v___x_3919_);
lean_dec(v_val_3917_);
lean_inc_n(v_stx_2334_, 2);
v___x_3952_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_3953_ = lean_st_ref_get(v_a_2340_);
v_env_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_ref(v_env_3954_);
lean_dec(v___x_3953_);
v___x_3955_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3956_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3955_, v_env_3954_, v___x_3952_);
v___x_3957_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3958_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_3956_, v___x_3957_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_3956_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3989_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3989_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3989_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_fst_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3987_; 
v_fst_3963_ = lean_ctor_get(v_a_3959_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_a_3959_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v_a_3959_, 1);
lean_dec(v_unused_3988_);
v___x_3965_ = v_a_3959_;
v_isShared_3966_ = v_isSharedCheck_3987_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_fst_3963_);
lean_dec(v_a_3959_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3987_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
if (lean_obj_tag(v_fst_3963_) == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3970_; 
lean_del_object(v___x_3961_);
v___x_3967_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3968_ = l_Lean_MessageData_ofName(v___x_3952_);
lean_inc_ref(v___x_3968_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 7);
lean_ctor_set(v___x_3965_, 1, v___x_3968_);
lean_ctor_set(v___x_3965_, 0, v___x_3967_);
v___x_3970_ = v___x_3965_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3971_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3970_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_3974_ = l_Lean_indentD(v___x_3973_);
v___x_3975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3972_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set(v___x_3978_, 1, v___x_3968_);
v___x_3979_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3980_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_3981_;
}
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3985_; 
lean_del_object(v___x_3965_);
lean_dec(v___x_3952_);
lean_dec(v_stx_2334_);
v_val_3983_ = lean_ctor_get(v_fst_3963_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v_fst_3963_, 1);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 0, v_val_3983_);
v___x_3985_ = v___x_3961_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_val_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v___x_3952_);
lean_dec(v_stx_2334_);
v_a_3990_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3958_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3958_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
lean_dec(v_stx_2334_);
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = l_Lean_Syntax_getArg(v___x_3948_, v___x_3998_);
lean_dec(v___x_3948_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3999_);
v___x_4001_ = v___x_3919_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
v_elseSeq_x3f_3924_ = v___x_4001_;
v___y_3925_ = v_a_2335_;
v___y_3926_ = v_a_2336_;
v___y_3927_ = v_a_2337_;
v___y_3928_ = v_a_2338_;
v___y_3929_ = v_a_2339_;
v___y_3930_ = v_a_2340_;
goto v___jp_3923_;
}
}
}
else
{
lean_object* v___x_4003_; 
lean_dec(v___x_3948_);
lean_del_object(v___x_3919_);
lean_dec(v_stx_2334_);
v___x_4003_ = lean_box(0);
v_elseSeq_x3f_3924_ = v___x_4003_;
v___y_3925_ = v_a_2335_;
v___y_3926_ = v_a_2336_;
v___y_3927_ = v_a_2337_;
v___y_3928_ = v_a_2338_;
v___y_3929_ = v_a_2339_;
v___y_3930_ = v_a_2340_;
goto v___jp_3923_;
}
v___jp_3923_:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; size_t v_sz_3934_; lean_object* v___x_3935_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = l_Array_reverse___redArg(v_val_3917_);
v_sz_3934_ = lean_array_size(v___x_3933_);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3933_, v_sz_3934_, v___x_3869_, v_a_3932_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec_ref(v___x_3933_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3922_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3946_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3946_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3946_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3938_, v_a_3936_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3942_);
v___x_3944_ = v___x_3940_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
else
{
lean_dec(v_a_3936_);
return v___x_3937_;
}
}
else
{
lean_dec(v___x_3922_);
return v___x_3935_;
}
}
else
{
lean_dec(v___x_3922_);
lean_dec(v_val_3917_);
return v___x_3931_;
}
}
}
}
}
}
else
{
lean_object* v___x_4005_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___x_4069_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4176_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4069_);
v___x_4177_ = l_Lean_Syntax_isNone(v___x_4176_);
if (v___x_4177_ == 0)
{
uint8_t v___x_4178_; 
lean_inc(v___x_4176_);
v___x_4178_ = l_Lean_Syntax_matchesNull(v___x_4176_, v___x_4069_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v_env_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec(v___x_4176_);
lean_inc_n(v_stx_2334_, 2);
v___x_4179_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4180_ = lean_st_ref_get(v_a_2340_);
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc_ref(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4183_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4182_, v_env_4181_, v___x_4179_);
v___x_4184_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4185_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4183_, v___x_4184_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4183_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4216_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4216_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4216_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v_fst_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4214_; 
v_fst_4190_ = lean_ctor_get(v_a_4186_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_a_4186_);
if (v_isSharedCheck_4214_ == 0)
{
lean_object* v_unused_4215_; 
v_unused_4215_ = lean_ctor_get(v_a_4186_, 1);
lean_dec(v_unused_4215_);
v___x_4192_ = v_a_4186_;
v_isShared_4193_ = v_isSharedCheck_4214_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_fst_4190_);
lean_dec(v_a_4186_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4214_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
if (lean_obj_tag(v_fst_4190_) == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
lean_del_object(v___x_4188_);
v___x_4194_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4195_ = l_Lean_MessageData_ofName(v___x_4179_);
lean_inc_ref(v___x_4195_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 7);
lean_ctor_set(v___x_4192_, 1, v___x_4195_);
lean_ctor_set(v___x_4192_, 0, v___x_4194_);
v___x_4197_ = v___x_4192_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4198_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4201_ = l_Lean_indentD(v___x_4200_);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4199_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v___x_4195_);
v___x_4206_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4207_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4208_;
}
}
else
{
lean_object* v_val_4210_; lean_object* v___x_4212_; 
lean_del_object(v___x_4192_);
lean_dec(v___x_4179_);
lean_dec(v_stx_2334_);
v_val_4210_ = lean_ctor_get(v_fst_4190_, 0);
lean_inc(v_val_4210_);
lean_dec_ref_known(v_fst_4190_, 1);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v_val_4210_);
v___x_4212_ = v___x_4188_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_val_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v___x_4179_);
lean_dec(v_stx_2334_);
v_a_4217_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4185_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4185_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v___x_4225_ = l_Lean_Syntax_getArg(v___x_4176_, v___x_4005_);
lean_dec(v___x_4176_);
v___x_4226_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4227_ = l_Lean_Syntax_isOfKind(v___x_4225_, v___x_4226_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_env_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4228_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4229_ = lean_st_ref_get(v_a_2340_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref(v_env_4230_);
lean_dec(v___x_4229_);
v___x_4231_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4232_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4231_, v_env_4230_, v___x_4228_);
v___x_4233_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4234_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4232_, v___x_4233_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4232_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4265_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4265_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4265_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v_fst_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4263_; 
v_fst_4239_ = lean_ctor_get(v_a_4235_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_a_4235_);
if (v_isSharedCheck_4263_ == 0)
{
lean_object* v_unused_4264_; 
v_unused_4264_ = lean_ctor_get(v_a_4235_, 1);
lean_dec(v_unused_4264_);
v___x_4241_ = v_a_4235_;
v_isShared_4242_ = v_isSharedCheck_4263_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_fst_4239_);
lean_dec(v_a_4235_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4263_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
if (lean_obj_tag(v_fst_4239_) == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_del_object(v___x_4237_);
v___x_4243_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4244_ = l_Lean_MessageData_ofName(v___x_4228_);
lean_inc_ref(v___x_4244_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 7);
lean_ctor_set(v___x_4241_, 1, v___x_4244_);
lean_ctor_set(v___x_4241_, 0, v___x_4243_);
v___x_4246_ = v___x_4241_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4247_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4250_ = l_Lean_indentD(v___x_4249_);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4248_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
lean_ctor_set(v___x_4254_, 1, v___x_4244_);
v___x_4255_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4256_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4257_;
}
}
else
{
lean_object* v_val_4259_; lean_object* v___x_4261_; 
lean_del_object(v___x_4241_);
lean_dec(v___x_4228_);
lean_dec(v_stx_2334_);
v_val_4259_ = lean_ctor_get(v_fst_4239_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v_fst_4239_, 1);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 0, v_val_4259_);
v___x_4261_ = v___x_4237_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_val_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v___x_4228_);
lean_dec(v_stx_2334_);
v_a_4266_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4234_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4234_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
v___y_4071_ = v_a_2335_;
v___y_4072_ = v_a_2336_;
v___y_4073_ = v_a_2337_;
v___y_4074_ = v_a_2338_;
v___y_4075_ = v_a_2339_;
v___y_4076_ = v_a_2340_;
goto v___jp_4070_;
}
}
}
else
{
lean_dec(v___x_4176_);
v___y_4071_ = v_a_2335_;
v___y_4072_ = v_a_2336_;
v___y_4073_ = v_a_2337_;
v___y_4074_ = v_a_2338_;
v___y_4075_ = v_a_2339_;
v___y_4076_ = v_a_2340_;
goto v___jp_4070_;
}
v___jp_4006_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; 
v___x_4013_ = lean_unsigned_to_nat(6u);
v___x_4014_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4013_);
v___x_4015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_4014_);
v___x_4016_ = l_Lean_Syntax_isOfKind(v___x_4014_, v___x_4015_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v_env_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec(v___x_4014_);
lean_inc_n(v_stx_2334_, 2);
v___x_4017_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4018_ = lean_st_ref_get(v___y_4012_);
v_env_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc_ref(v_env_4019_);
lean_dec(v___x_4018_);
v___x_4020_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4021_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4020_, v_env_4019_, v___x_4017_);
v___x_4022_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4023_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4021_, v___x_4022_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___x_4021_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4054_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4054_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4054_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_fst_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4052_; 
v_fst_4028_ = lean_ctor_get(v_a_4024_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v_a_4024_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; 
v_unused_4053_ = lean_ctor_get(v_a_4024_, 1);
lean_dec(v_unused_4053_);
v___x_4030_ = v_a_4024_;
v_isShared_4031_ = v_isSharedCheck_4052_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_fst_4028_);
lean_dec(v_a_4024_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4052_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
if (lean_obj_tag(v_fst_4028_) == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
lean_del_object(v___x_4026_);
v___x_4032_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4033_ = l_Lean_MessageData_ofName(v___x_4017_);
lean_inc_ref(v___x_4033_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set_tag(v___x_4030_, 7);
lean_ctor_set(v___x_4030_, 1, v___x_4033_);
lean_ctor_set(v___x_4030_, 0, v___x_4032_);
v___x_4035_ = v___x_4030_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4036_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4039_ = l_Lean_indentD(v___x_4038_);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4037_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v___x_4033_);
v___x_4044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4045_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
return v___x_4046_;
}
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4050_; 
lean_del_object(v___x_4030_);
lean_dec(v___x_4017_);
lean_dec(v_stx_2334_);
v_val_4048_ = lean_ctor_get(v_fst_4028_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v_fst_4028_, 1);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v_val_4048_);
v___x_4050_ = v___x_4026_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_val_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v___x_4017_);
lean_dec(v_stx_2334_);
v_a_4055_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4023_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4023_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; size_t v_sz_4066_; size_t v___x_4067_; lean_object* v___x_4068_; 
lean_dec(v_stx_2334_);
v___x_4063_ = l_Lean_Syntax_getArg(v___x_4014_, v___x_4005_);
lean_dec(v___x_4014_);
v___x_4064_ = l_Lean_Syntax_getArgs(v___x_4063_);
lean_dec(v___x_4063_);
v___x_4065_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4066_ = lean_array_size(v___x_4064_);
v___x_4067_ = ((size_t)0ULL);
v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2737_, v___x_4064_, v_sz_4066_, v___x_4067_, v___x_4065_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec_ref(v___x_4064_);
return v___x_4068_;
}
}
v___jp_4070_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4077_ = lean_unsigned_to_nat(2u);
v___x_4078_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4077_);
v___x_4079_ = l_Lean_Syntax_isNone(v___x_4078_);
if (v___x_4079_ == 0)
{
uint8_t v___x_4080_; 
lean_inc(v___x_4078_);
v___x_4080_ = l_Lean_Syntax_matchesNull(v___x_4078_, v___x_4069_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v_env_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec(v___x_4078_);
lean_inc_n(v_stx_2334_, 2);
v___x_4081_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4082_ = lean_st_ref_get(v___y_4076_);
v_env_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4085_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4084_, v_env_4083_, v___x_4081_);
v___x_4086_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4087_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4085_, v___x_4086_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___x_4085_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4118_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4118_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4118_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v_fst_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4116_; 
v_fst_4092_ = lean_ctor_get(v_a_4088_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v_a_4088_, 1);
lean_dec(v_unused_4117_);
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4116_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_fst_4092_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4116_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
if (lean_obj_tag(v_fst_4092_) == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
lean_del_object(v___x_4090_);
v___x_4096_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4097_ = l_Lean_MessageData_ofName(v___x_4081_);
lean_inc_ref(v___x_4097_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 7);
lean_ctor_set(v___x_4094_, 1, v___x_4097_);
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4099_ = v___x_4094_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4100_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4103_ = l_Lean_indentD(v___x_4102_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4101_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v___x_4097_);
v___x_4108_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4109_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
return v___x_4110_;
}
}
else
{
lean_object* v_val_4112_; lean_object* v___x_4114_; 
lean_del_object(v___x_4094_);
lean_dec(v___x_4081_);
lean_dec(v_stx_2334_);
v_val_4112_ = lean_ctor_get(v_fst_4092_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v_fst_4092_, 1);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v_val_4112_);
v___x_4114_ = v___x_4090_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_val_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v___x_4081_);
lean_dec(v_stx_2334_);
v_a_4119_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4087_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4087_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4127_ = l_Lean_Syntax_getArg(v___x_4078_, v___x_4005_);
lean_dec(v___x_4078_);
v___x_4128_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4129_ = l_Lean_Syntax_isOfKind(v___x_4127_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v_env_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4130_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4131_ = lean_st_ref_get(v___y_4076_);
v_env_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc_ref(v_env_4132_);
lean_dec(v___x_4131_);
v___x_4133_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4134_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4133_, v_env_4132_, v___x_4130_);
v___x_4135_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4136_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4134_, v___x_4135_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___x_4134_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4167_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4167_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4167_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_fst_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4165_; 
v_fst_4141_ = lean_ctor_get(v_a_4137_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_a_4137_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_a_4137_, 1);
lean_dec(v_unused_4166_);
v___x_4143_ = v_a_4137_;
v_isShared_4144_ = v_isSharedCheck_4165_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_fst_4141_);
lean_dec(v_a_4137_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4165_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
if (lean_obj_tag(v_fst_4141_) == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
lean_del_object(v___x_4139_);
v___x_4145_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4146_ = l_Lean_MessageData_ofName(v___x_4130_);
lean_inc_ref(v___x_4146_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 7);
lean_ctor_set(v___x_4143_, 1, v___x_4146_);
lean_ctor_set(v___x_4143_, 0, v___x_4145_);
v___x_4148_ = v___x_4143_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4149_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4152_ = l_Lean_indentD(v___x_4151_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4150_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4146_);
v___x_4157_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4158_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
return v___x_4159_;
}
}
else
{
lean_object* v_val_4161_; lean_object* v___x_4163_; 
lean_del_object(v___x_4143_);
lean_dec(v___x_4130_);
lean_dec(v_stx_2334_);
v_val_4161_ = lean_ctor_get(v_fst_4141_, 0);
lean_inc(v_val_4161_);
lean_dec_ref_known(v_fst_4141_, 1);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v_val_4161_);
v___x_4163_ = v___x_4139_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_val_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v___x_4130_);
lean_dec(v_stx_2334_);
v_a_4168_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4136_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4136_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
v___y_4007_ = v___y_4071_;
v___y_4008_ = v___y_4072_;
v___y_4009_ = v___y_4073_;
v___y_4010_ = v___y_4074_;
v___y_4011_ = v___y_4075_;
v___y_4012_ = v___y_4076_;
goto v___jp_4006_;
}
}
}
else
{
lean_dec(v___x_4078_);
v___y_4007_ = v___y_4071_;
v___y_4008_ = v___y_4072_;
v___y_4009_ = v___y_4073_;
v___y_4010_ = v___y_4074_;
v___y_4011_ = v___y_4075_;
v___y_4012_ = v___y_4076_;
goto v___jp_4006_;
}
}
}
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4274_);
if (v___x_2735_ == 0)
{
lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4276_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4275_);
v___x_4277_ = l_Lean_Syntax_isOfKind(v___x_4275_, v___x_4276_);
if (v___x_4277_ == 0)
{
if (v___x_2735_ == 0)
{
lean_object* v___x_4278_; uint8_t v___x_4279_; 
v___x_4278_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4275_);
v___x_4279_ = l_Lean_Syntax_isOfKind(v___x_4275_, v___x_4278_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v_env_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_dec(v___x_4275_);
lean_inc_n(v_stx_2334_, 2);
v___x_4280_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4281_ = lean_st_ref_get(v_a_2340_);
v_env_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc_ref(v_env_4282_);
lean_dec(v___x_4281_);
v___x_4283_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4284_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4283_, v_env_4282_, v___x_4280_);
v___x_4285_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4286_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4284_, v___x_4285_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4284_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4317_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4289_ = v___x_4286_;
v_isShared_4290_ = v_isSharedCheck_4317_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4286_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4317_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v_fst_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4315_; 
v_fst_4291_ = lean_ctor_get(v_a_4287_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v_a_4287_);
if (v_isSharedCheck_4315_ == 0)
{
lean_object* v_unused_4316_; 
v_unused_4316_ = lean_ctor_get(v_a_4287_, 1);
lean_dec(v_unused_4316_);
v___x_4293_ = v_a_4287_;
v_isShared_4294_ = v_isSharedCheck_4315_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_fst_4291_);
lean_dec(v_a_4287_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4315_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
if (lean_obj_tag(v_fst_4291_) == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4298_; 
lean_del_object(v___x_4289_);
v___x_4295_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4296_ = l_Lean_MessageData_ofName(v___x_4280_);
lean_inc_ref(v___x_4296_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 7);
lean_ctor_set(v___x_4293_, 1, v___x_4296_);
lean_ctor_set(v___x_4293_, 0, v___x_4295_);
v___x_4298_ = v___x_4293_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4295_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4299_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4302_ = l_Lean_indentD(v___x_4301_);
v___x_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4300_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_4304_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___x_4296_);
v___x_4307_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4308_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4309_;
}
}
else
{
lean_object* v_val_4311_; lean_object* v___x_4313_; 
lean_del_object(v___x_4293_);
lean_dec(v___x_4280_);
lean_dec(v_stx_2334_);
v_val_4311_ = lean_ctor_get(v_fst_4291_, 0);
lean_inc(v_val_4311_);
lean_dec_ref_known(v_fst_4291_, 1);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 0, v_val_4311_);
v___x_4313_ = v___x_4289_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_val_4311_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v___x_4280_);
lean_dec(v_stx_2334_);
v_a_4318_ = lean_ctor_get(v___x_4286_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4286_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4286_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
else
{
lean_object* v___x_4326_; 
lean_dec(v_stx_2334_);
v___x_4326_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2424_, v___x_4275_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4326_;
}
}
else
{
lean_object* v___x_4327_; 
lean_dec(v_stx_2334_);
v___x_4327_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2424_, v___x_4275_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4327_;
}
}
else
{
lean_object* v___x_4328_; 
lean_dec(v_stx_2334_);
v___x_4328_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2424_, v___x_4275_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4328_;
}
}
else
{
lean_object* v___x_4329_; 
lean_dec(v_stx_2334_);
v___x_4329_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2424_, v___x_4275_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4329_;
}
}
}
else
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = lean_unsigned_to_nat(0u);
v___x_4331_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4330_);
if (v___x_2733_ == 0)
{
lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4331_);
v___x_4359_ = l_Lean_Syntax_isOfKind(v___x_4331_, v___x_4358_);
if (v___x_4359_ == 0)
{
if (v___x_2733_ == 0)
{
lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4360_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4331_);
v___x_4361_ = l_Lean_Syntax_isOfKind(v___x_4331_, v___x_4360_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v_env_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_dec(v___x_4331_);
lean_inc_n(v_stx_2334_, 2);
v___x_4362_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4363_ = lean_st_ref_get(v_a_2340_);
v_env_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc_ref(v_env_4364_);
lean_dec(v___x_4363_);
v___x_4365_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4366_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4365_, v_env_4364_, v___x_4362_);
v___x_4367_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4368_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4366_, v___x_4367_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4366_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4399_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4399_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4399_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v_fst_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4397_; 
v_fst_4373_ = lean_ctor_get(v_a_4369_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_a_4369_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v_a_4369_, 1);
lean_dec(v_unused_4398_);
v___x_4375_ = v_a_4369_;
v_isShared_4376_ = v_isSharedCheck_4397_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_fst_4373_);
lean_dec(v_a_4369_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4397_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
if (lean_obj_tag(v_fst_4373_) == 0)
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4380_; 
lean_del_object(v___x_4371_);
v___x_4377_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4378_ = l_Lean_MessageData_ofName(v___x_4362_);
lean_inc_ref(v___x_4378_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 7);
lean_ctor_set(v___x_4375_, 1, v___x_4378_);
lean_ctor_set(v___x_4375_, 0, v___x_4377_);
v___x_4380_ = v___x_4375_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4392_, 1, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4381_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4380_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4384_ = l_Lean_indentD(v___x_4383_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4382_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___x_4378_);
v___x_4389_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4390_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4391_;
}
}
else
{
lean_object* v_val_4393_; lean_object* v___x_4395_; 
lean_del_object(v___x_4375_);
lean_dec(v___x_4362_);
lean_dec(v_stx_2334_);
v_val_4393_ = lean_ctor_get(v_fst_4373_, 0);
lean_inc(v_val_4393_);
lean_dec_ref_known(v_fst_4373_, 1);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v_val_4393_);
v___x_4395_ = v___x_4371_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_val_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v___x_4362_);
lean_dec(v_stx_2334_);
v_a_4400_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4368_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4368_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_4332_;
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_4332_;
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_4345_;
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_4345_;
}
v___jp_4332_:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4331_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4331_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = lean_box(0);
v___x_4336_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4334_, v___x_4335_, v___x_4335_, v___x_4335_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4336_;
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4333_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4333_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
v___jp_4345_:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4331_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4331_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
v___x_4348_ = lean_box(0);
v___x_4349_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4347_, v___x_4348_, v___x_4348_, v___x_4348_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4349_;
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_a_4350_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4346_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4346_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
}
else
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v___x_4408_ = lean_unsigned_to_nat(0u);
v___x_4409_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4408_);
v___x_4410_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4409_);
v___x_4411_ = l_Lean_Syntax_isOfKind(v___x_4409_, v___x_4410_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v_env_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_dec(v___x_4409_);
lean_inc_n(v_stx_2334_, 2);
v___x_4412_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4413_ = lean_st_ref_get(v_a_2340_);
v_env_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc_ref(v_env_4414_);
lean_dec(v___x_4413_);
v___x_4415_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4416_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4415_, v_env_4414_, v___x_4412_);
v___x_4417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4418_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4416_, v___x_4417_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4416_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4449_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4449_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4449_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v_fst_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4447_; 
v_fst_4423_ = lean_ctor_get(v_a_4419_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_a_4419_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v_a_4419_, 1);
lean_dec(v_unused_4448_);
v___x_4425_ = v_a_4419_;
v_isShared_4426_ = v_isSharedCheck_4447_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_fst_4423_);
lean_dec(v_a_4419_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4447_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
if (lean_obj_tag(v_fst_4423_) == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
lean_del_object(v___x_4421_);
v___x_4427_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4428_ = l_Lean_MessageData_ofName(v___x_4412_);
lean_inc_ref(v___x_4428_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set_tag(v___x_4425_, 7);
lean_ctor_set(v___x_4425_, 1, v___x_4428_);
lean_ctor_set(v___x_4425_, 0, v___x_4427_);
v___x_4430_ = v___x_4425_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4427_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4431_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4430_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4434_ = l_Lean_indentD(v___x_4433_);
v___x_4435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4432_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
lean_ctor_set(v___x_4438_, 1, v___x_4428_);
v___x_4439_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4438_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
v___x_4441_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4440_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4441_;
}
}
else
{
lean_object* v_val_4443_; lean_object* v___x_4445_; 
lean_del_object(v___x_4425_);
lean_dec(v___x_4412_);
lean_dec(v_stx_2334_);
v_val_4443_ = lean_ctor_get(v_fst_4423_, 0);
lean_inc(v_val_4443_);
lean_dec_ref_known(v_fst_4423_, 1);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v_val_4443_);
v___x_4445_ = v___x_4421_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_val_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v___x_4412_);
lean_dec(v_stx_2334_);
v_a_4450_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4418_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4418_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v___x_4458_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4458_ = lean_unsigned_to_nat(1u);
v___x_4564_ = l_Lean_Syntax_getArg(v___x_4409_, v___x_4458_);
lean_dec(v___x_4409_);
v___x_4565_ = l_Lean_Syntax_isNone(v___x_4564_);
if (v___x_4565_ == 0)
{
uint8_t v___x_4566_; 
v___x_4566_ = l_Lean_Syntax_matchesNull(v___x_4564_, v___x_4458_);
if (v___x_4566_ == 0)
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v_env_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4567_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4568_ = lean_st_ref_get(v_a_2340_);
v_env_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4569_);
lean_dec(v___x_4568_);
v___x_4570_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4571_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4570_, v_env_4569_, v___x_4567_);
v___x_4572_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4573_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4571_, v___x_4572_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4571_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4604_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4604_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4604_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_fst_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4602_; 
v_fst_4578_ = lean_ctor_get(v_a_4574_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_a_4574_);
if (v_isSharedCheck_4602_ == 0)
{
lean_object* v_unused_4603_; 
v_unused_4603_ = lean_ctor_get(v_a_4574_, 1);
lean_dec(v_unused_4603_);
v___x_4580_ = v_a_4574_;
v_isShared_4581_ = v_isSharedCheck_4602_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_fst_4578_);
lean_dec(v_a_4574_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4602_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
if (lean_obj_tag(v_fst_4578_) == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
lean_del_object(v___x_4576_);
v___x_4582_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4583_ = l_Lean_MessageData_ofName(v___x_4567_);
lean_inc_ref(v___x_4583_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set_tag(v___x_4580_, 7);
lean_ctor_set(v___x_4580_, 1, v___x_4583_);
lean_ctor_set(v___x_4580_, 0, v___x_4582_);
v___x_4585_ = v___x_4580_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v___x_4583_);
v___x_4585_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4586_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4585_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4589_ = l_Lean_indentD(v___x_4588_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4587_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
lean_ctor_set(v___x_4593_, 1, v___x_4583_);
v___x_4594_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4595_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4596_;
}
}
else
{
lean_object* v_val_4598_; lean_object* v___x_4600_; 
lean_del_object(v___x_4580_);
lean_dec(v___x_4567_);
lean_dec(v_stx_2334_);
v_val_4598_ = lean_ctor_get(v_fst_4578_, 0);
lean_inc(v_val_4598_);
lean_dec_ref_known(v_fst_4578_, 1);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v_val_4598_);
v___x_4600_ = v___x_4576_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_val_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec(v___x_4567_);
lean_dec(v_stx_2334_);
v_a_4605_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4573_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4573_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
else
{
v___y_4460_ = v_a_2335_;
v___y_4461_ = v_a_2336_;
v___y_4462_ = v_a_2337_;
v___y_4463_ = v_a_2338_;
v___y_4464_ = v_a_2339_;
v___y_4465_ = v_a_2340_;
goto v___jp_4459_;
}
}
else
{
lean_dec(v___x_4564_);
v___y_4460_ = v_a_2335_;
v___y_4461_ = v_a_2336_;
v___y_4462_ = v_a_2337_;
v___y_4463_ = v_a_2338_;
v___y_4464_ = v_a_2339_;
v___y_4465_ = v_a_2340_;
goto v___jp_4459_;
}
v___jp_4459_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4466_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4458_);
v___x_4467_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4466_);
v___x_4468_ = l_Lean_Syntax_isOfKind(v___x_4466_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v_env_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec(v___x_4466_);
lean_inc_n(v_stx_2334_, 2);
v___x_4469_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4470_ = lean_st_ref_get(v___y_4465_);
v_env_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc_ref(v_env_4471_);
lean_dec(v___x_4470_);
v___x_4472_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4473_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4472_, v_env_4471_, v___x_4469_);
v___x_4474_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4475_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4473_, v___x_4474_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___x_4473_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4506_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4478_ = v___x_4475_;
v_isShared_4479_ = v_isSharedCheck_4506_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4475_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4506_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v_fst_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4504_; 
v_fst_4480_ = lean_ctor_get(v_a_4476_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_a_4476_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v_a_4476_, 1);
lean_dec(v_unused_4505_);
v___x_4482_ = v_a_4476_;
v_isShared_4483_ = v_isSharedCheck_4504_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_fst_4480_);
lean_dec(v_a_4476_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4504_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
if (lean_obj_tag(v_fst_4480_) == 0)
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
lean_del_object(v___x_4478_);
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4485_ = l_Lean_MessageData_ofName(v___x_4469_);
lean_inc_ref(v___x_4485_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set_tag(v___x_4482_, 7);
lean_ctor_set(v___x_4482_, 1, v___x_4485_);
lean_ctor_set(v___x_4482_, 0, v___x_4484_);
v___x_4487_ = v___x_4482_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4488_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4487_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4491_ = l_Lean_indentD(v___x_4490_);
v___x_4492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4489_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
lean_ctor_set(v___x_4495_, 1, v___x_4485_);
v___x_4496_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4495_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4497_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
return v___x_4498_;
}
}
else
{
lean_object* v_val_4500_; lean_object* v___x_4502_; 
lean_del_object(v___x_4482_);
lean_dec(v___x_4469_);
lean_dec(v_stx_2334_);
v_val_4500_ = lean_ctor_get(v_fst_4480_, 0);
lean_inc(v_val_4500_);
lean_dec_ref_known(v_fst_4480_, 1);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v_val_4500_);
v___x_4502_ = v___x_4478_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_val_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v___x_4469_);
lean_dec(v_stx_2334_);
v_a_4507_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4475_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4475_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
else
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = l_Lean_Syntax_getArg(v___x_4466_, v___x_4458_);
lean_dec(v___x_4466_);
v___x_4516_ = l_Lean_Syntax_isNone(v___x_4515_);
if (v___x_4516_ == 0)
{
uint8_t v___x_4517_; 
v___x_4517_ = l_Lean_Syntax_matchesNull(v___x_4515_, v___x_4458_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v_env_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4518_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4519_ = lean_st_ref_get(v___y_4465_);
v_env_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc_ref(v_env_4520_);
lean_dec(v___x_4519_);
v___x_4521_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4522_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4521_, v_env_4520_, v___x_4518_);
v___x_4523_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4524_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4522_, v___x_4523_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___x_4522_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4555_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4527_ = v___x_4524_;
v_isShared_4528_ = v_isSharedCheck_4555_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4524_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4555_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_fst_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4553_; 
v_fst_4529_ = lean_ctor_get(v_a_4525_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_a_4525_);
if (v_isSharedCheck_4553_ == 0)
{
lean_object* v_unused_4554_; 
v_unused_4554_ = lean_ctor_get(v_a_4525_, 1);
lean_dec(v_unused_4554_);
v___x_4531_ = v_a_4525_;
v_isShared_4532_ = v_isSharedCheck_4553_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_fst_4529_);
lean_dec(v_a_4525_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4553_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
if (lean_obj_tag(v_fst_4529_) == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
lean_del_object(v___x_4527_);
v___x_4533_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4534_ = l_Lean_MessageData_ofName(v___x_4518_);
lean_inc_ref(v___x_4534_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 7);
lean_ctor_set(v___x_4531_, 1, v___x_4534_);
lean_ctor_set(v___x_4531_, 0, v___x_4533_);
v___x_4536_ = v___x_4531_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4537_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4536_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4540_ = l_Lean_indentD(v___x_4539_);
v___x_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4538_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
v___x_4544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
lean_ctor_set(v___x_4544_, 1, v___x_4534_);
v___x_4545_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4544_);
lean_ctor_set(v___x_4546_, 1, v___x_4545_);
v___x_4547_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4546_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
return v___x_4547_;
}
}
else
{
lean_object* v_val_4549_; lean_object* v___x_4551_; 
lean_del_object(v___x_4531_);
lean_dec(v___x_4518_);
lean_dec(v_stx_2334_);
v_val_4549_ = lean_ctor_get(v_fst_4529_, 0);
lean_inc(v_val_4549_);
lean_dec_ref_known(v_fst_4529_, 1);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v_val_4549_);
v___x_4551_ = v___x_4527_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_val_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v___x_4518_);
lean_dec(v_stx_2334_);
v_a_4556_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4524_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4524_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2384_;
}
}
else
{
lean_dec(v___x_4515_);
lean_dec(v_stx_2334_);
goto v___jp_2384_;
}
}
}
}
}
}
else
{
lean_object* v___x_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v___x_4613_ = lean_unsigned_to_nat(1u);
v___x_4614_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4613_);
v___x_4615_ = l_Lean_Syntax_isNone(v___x_4614_);
if (v___x_4615_ == 0)
{
uint8_t v___x_4616_; 
v___x_4616_ = l_Lean_Syntax_matchesNull(v___x_4614_, v___x_4613_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v_env_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4617_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4618_ = lean_st_ref_get(v_a_2340_);
v_env_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_ref(v_env_4619_);
lean_dec(v___x_4618_);
v___x_4620_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4621_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4620_, v_env_4619_, v___x_4617_);
v___x_4622_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4621_, v___x_4622_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4621_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4654_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4654_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4654_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v_fst_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4652_; 
v_fst_4628_ = lean_ctor_get(v_a_4624_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_a_4624_);
if (v_isSharedCheck_4652_ == 0)
{
lean_object* v_unused_4653_; 
v_unused_4653_ = lean_ctor_get(v_a_4624_, 1);
lean_dec(v_unused_4653_);
v___x_4630_ = v_a_4624_;
v_isShared_4631_ = v_isSharedCheck_4652_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_fst_4628_);
lean_dec(v_a_4624_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4652_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
if (lean_obj_tag(v_fst_4628_) == 0)
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
lean_del_object(v___x_4626_);
v___x_4632_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4633_ = l_Lean_MessageData_ofName(v___x_4617_);
lean_inc_ref(v___x_4633_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set_tag(v___x_4630_, 7);
lean_ctor_set(v___x_4630_, 1, v___x_4633_);
lean_ctor_set(v___x_4630_, 0, v___x_4632_);
v___x_4635_ = v___x_4630_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4636_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4639_ = l_Lean_indentD(v___x_4638_);
v___x_4640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4637_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
v___x_4641_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
lean_ctor_set(v___x_4643_, 1, v___x_4633_);
v___x_4644_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4643_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4645_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4646_;
}
}
else
{
lean_object* v_val_4648_; lean_object* v___x_4650_; 
lean_del_object(v___x_4630_);
lean_dec(v___x_4617_);
lean_dec(v_stx_2334_);
v_val_4648_ = lean_ctor_get(v_fst_4628_, 0);
lean_inc(v_val_4648_);
lean_dec_ref_known(v_fst_4628_, 1);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v_val_4648_);
v___x_4650_ = v___x_4626_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_val_4648_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec(v___x_4617_);
lean_dec(v_stx_2334_);
v_a_4655_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4623_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4623_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
v___y_2674_ = v_a_2335_;
v___y_2675_ = v_a_2336_;
v___y_2676_ = v_a_2337_;
v___y_2677_ = v_a_2338_;
v___y_2678_ = v_a_2339_;
v___y_2679_ = v_a_2340_;
goto v___jp_2673_;
}
}
else
{
lean_dec(v___x_4614_);
v___y_2674_ = v_a_2335_;
v___y_2675_ = v_a_2336_;
v___y_2676_ = v_a_2337_;
v___y_2677_ = v_a_2338_;
v___y_2678_ = v_a_2339_;
v___y_2679_ = v_a_2340_;
goto v___jp_2673_;
}
}
}
else
{
lean_object* v___x_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v___x_4663_ = lean_unsigned_to_nat(1u);
v___x_4664_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4663_);
v___x_4665_ = l_Lean_Syntax_isNone(v___x_4664_);
if (v___x_4665_ == 0)
{
uint8_t v___x_4666_; 
v___x_4666_ = l_Lean_Syntax_matchesNull(v___x_4664_, v___x_4663_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v_env_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4667_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4668_ = lean_st_ref_get(v_a_2340_);
v_env_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc_ref(v_env_4669_);
lean_dec(v___x_4668_);
v___x_4670_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4671_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4670_, v_env_4669_, v___x_4667_);
v___x_4672_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4673_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4671_, v___x_4672_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4671_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4704_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4704_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4704_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v_fst_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4702_; 
v_fst_4678_ = lean_ctor_get(v_a_4674_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_a_4674_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v_a_4674_, 1);
lean_dec(v_unused_4703_);
v___x_4680_ = v_a_4674_;
v_isShared_4681_ = v_isSharedCheck_4702_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_fst_4678_);
lean_dec(v_a_4674_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4702_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
if (lean_obj_tag(v_fst_4678_) == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4685_; 
lean_del_object(v___x_4676_);
v___x_4682_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4683_ = l_Lean_MessageData_ofName(v___x_4667_);
lean_inc_ref(v___x_4683_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 7);
lean_ctor_set(v___x_4680_, 1, v___x_4683_);
lean_ctor_set(v___x_4680_, 0, v___x_4682_);
v___x_4685_ = v___x_4680_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4686_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4685_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4689_ = l_Lean_indentD(v___x_4688_);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4687_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
v___x_4691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v___x_4683_);
v___x_4694_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4693_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
v___x_4696_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4695_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4696_;
}
}
else
{
lean_object* v_val_4698_; lean_object* v___x_4700_; 
lean_del_object(v___x_4680_);
lean_dec(v___x_4667_);
lean_dec(v_stx_2334_);
v_val_4698_ = lean_ctor_get(v_fst_4678_, 0);
lean_inc(v_val_4698_);
lean_dec_ref_known(v_fst_4678_, 1);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v_val_4698_);
v___x_4700_ = v___x_4676_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_val_4698_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec(v___x_4667_);
lean_dec(v_stx_2334_);
v_a_4705_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4673_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4673_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
else
{
v___y_2605_ = v_a_2335_;
v___y_2606_ = v_a_2336_;
v___y_2607_ = v_a_2337_;
v___y_2608_ = v_a_2338_;
v___y_2609_ = v_a_2339_;
v___y_2610_ = v_a_2340_;
goto v___jp_2604_;
}
}
else
{
lean_dec(v___x_4664_);
v___y_2605_ = v_a_2335_;
v___y_2606_ = v_a_2336_;
v___y_2607_ = v_a_2337_;
v___y_2608_ = v_a_2338_;
v___y_2609_ = v_a_2339_;
v___y_2610_ = v_a_2340_;
goto v___jp_2604_;
}
}
v___jp_2663_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_unsigned_to_nat(3u);
v___x_2671_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2670_);
lean_dec(v_stx_2334_);
v___x_2672_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2662_, v___x_2671_, v___y_2666_, v___y_2669_, v___y_2665_, v___y_2667_, v___y_2664_, v___y_2668_);
return v___x_2672_;
}
v___jp_2673_:
{
if (v___x_2662_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2680_ = lean_unsigned_to_nat(2u);
v___x_2681_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2680_);
v___x_2682_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2683_ = l_Lean_Syntax_isOfKind(v___x_2681_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v_env_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2684_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2685_ = lean_st_ref_get(v___y_2679_);
v_env_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2685_);
v___x_2687_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2688_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2687_, v_env_2686_, v___x_2684_);
v___x_2689_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2690_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2688_, v___x_2689_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___x_2688_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2721_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2721_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2721_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_fst_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2719_; 
v_fst_2695_ = lean_ctor_get(v_a_2691_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_a_2691_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_a_2691_, 1);
lean_dec(v_unused_2720_);
v___x_2697_ = v_a_2691_;
v_isShared_2698_ = v_isSharedCheck_2719_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_fst_2695_);
lean_dec(v_a_2691_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2719_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
if (lean_obj_tag(v_fst_2695_) == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_del_object(v___x_2693_);
v___x_2699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2700_ = l_Lean_MessageData_ofName(v___x_2684_);
lean_inc_ref(v___x_2700_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 7);
lean_ctor_set(v___x_2697_, 1, v___x_2700_);
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2706_ = l_Lean_indentD(v___x_2705_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2704_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2700_);
v___x_2711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2712_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
return v___x_2713_;
}
}
else
{
lean_object* v_val_2715_; lean_object* v___x_2717_; 
lean_del_object(v___x_2697_);
lean_dec(v___x_2684_);
lean_dec(v_stx_2334_);
v_val_2715_ = lean_ctor_get(v_fst_2695_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v_fst_2695_, 1);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v_val_2715_);
v___x_2717_ = v___x_2693_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_val_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___x_2684_);
lean_dec(v_stx_2334_);
v_a_2722_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2690_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2690_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
v___y_2664_ = v___y_2678_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2674_;
v___y_2667_ = v___y_2677_;
v___y_2668_ = v___y_2679_;
v___y_2669_ = v___y_2675_;
goto v___jp_2663_;
}
}
else
{
v___y_2664_ = v___y_2678_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2674_;
v___y_2667_ = v___y_2677_;
v___y_2668_ = v___y_2679_;
v___y_2669_ = v___y_2675_;
goto v___jp_2663_;
}
}
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; 
v___x_4713_ = lean_unsigned_to_nat(0u);
v___x_4714_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4713_);
v___x_4715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4716_ = l_Lean_Syntax_isOfKind(v___x_4714_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v_env_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
lean_del_object(v___x_2398_);
lean_inc_n(v_stx_2334_, 2);
v___x_4717_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4718_ = lean_st_ref_get(v_a_2340_);
v_env_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc_ref(v_env_4719_);
lean_dec(v___x_4718_);
v___x_4720_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4721_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4720_, v_env_4719_, v___x_4717_);
v___x_4722_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4723_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4721_, v___x_4722_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4721_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4754_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4726_ = v___x_4723_;
v_isShared_4727_ = v_isSharedCheck_4754_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4723_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4754_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v_fst_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4752_; 
v_fst_4728_ = lean_ctor_get(v_a_4724_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_a_4724_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; 
v_unused_4753_ = lean_ctor_get(v_a_4724_, 1);
lean_dec(v_unused_4753_);
v___x_4730_ = v_a_4724_;
v_isShared_4731_ = v_isSharedCheck_4752_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_fst_4728_);
lean_dec(v_a_4724_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4752_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
if (lean_obj_tag(v_fst_4728_) == 0)
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
lean_del_object(v___x_4726_);
v___x_4732_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4733_ = l_Lean_MessageData_ofName(v___x_4717_);
lean_inc_ref(v___x_4733_);
if (v_isShared_4731_ == 0)
{
lean_ctor_set_tag(v___x_4730_, 7);
lean_ctor_set(v___x_4730_, 1, v___x_4733_);
lean_ctor_set(v___x_4730_, 0, v___x_4732_);
v___x_4735_ = v___x_4730_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4732_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v___x_4733_);
v___x_4735_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4736_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4735_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4739_ = l_Lean_indentD(v___x_4738_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4737_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
lean_ctor_set(v___x_4743_, 1, v___x_4733_);
v___x_4744_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v___x_4744_);
v___x_4746_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4745_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4746_;
}
}
else
{
lean_object* v_val_4748_; lean_object* v___x_4750_; 
lean_del_object(v___x_4730_);
lean_dec(v___x_4717_);
lean_dec(v_stx_2334_);
v_val_4748_ = lean_ctor_get(v_fst_4728_, 0);
lean_inc(v_val_4748_);
lean_dec_ref_known(v_fst_4728_, 1);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v_val_4748_);
v___x_4750_ = v___x_4726_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_val_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v___x_4717_);
lean_dec(v_stx_2334_);
v_a_4755_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4723_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4723_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
else
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4763_ = lean_unsigned_to_nat(1u);
v___x_4764_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4763_);
v___x_4765_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4764_);
v___x_4766_ = l_Lean_Syntax_isOfKind(v___x_4764_, v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v_env_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
lean_dec(v___x_4764_);
lean_del_object(v___x_2398_);
lean_inc_n(v_stx_2334_, 2);
v___x_4767_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4768_ = lean_st_ref_get(v_a_2340_);
v_env_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc_ref(v_env_4769_);
lean_dec(v___x_4768_);
v___x_4770_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4771_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4770_, v_env_4769_, v___x_4767_);
v___x_4772_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4773_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4771_, v___x_4772_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4771_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4804_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4776_ = v___x_4773_;
v_isShared_4777_ = v_isSharedCheck_4804_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4773_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4804_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v_fst_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4802_; 
v_fst_4778_ = lean_ctor_get(v_a_4774_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_a_4774_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; 
v_unused_4803_ = lean_ctor_get(v_a_4774_, 1);
lean_dec(v_unused_4803_);
v___x_4780_ = v_a_4774_;
v_isShared_4781_ = v_isSharedCheck_4802_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_fst_4778_);
lean_dec(v_a_4774_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4802_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
if (lean_obj_tag(v_fst_4778_) == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
lean_del_object(v___x_4776_);
v___x_4782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4783_ = l_Lean_MessageData_ofName(v___x_4767_);
lean_inc_ref(v___x_4783_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set_tag(v___x_4780_, 7);
lean_ctor_set(v___x_4780_, 1, v___x_4783_);
lean_ctor_set(v___x_4780_, 0, v___x_4782_);
v___x_4785_ = v___x_4780_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4786_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4785_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4789_ = l_Lean_indentD(v___x_4788_);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4787_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4790_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v___x_4793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set(v___x_4793_, 1, v___x_4783_);
v___x_4794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4793_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4795_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4796_;
}
}
else
{
lean_object* v_val_4798_; lean_object* v___x_4800_; 
lean_del_object(v___x_4780_);
lean_dec(v___x_4767_);
lean_dec(v_stx_2334_);
v_val_4798_ = lean_ctor_get(v_fst_4778_, 0);
lean_inc(v_val_4798_);
lean_dec_ref_known(v_fst_4778_, 1);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v_val_4798_);
v___x_4800_ = v___x_4776_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_val_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec(v___x_4767_);
lean_dec(v_stx_2334_);
v_a_4805_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4773_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4773_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v___x_4813_; uint8_t v___x_4814_; 
v___x_4813_ = l_Lean_Syntax_getArg(v___x_4764_, v___x_4713_);
lean_dec(v___x_4764_);
lean_inc(v___x_4813_);
v___x_4814_ = l_Lean_Syntax_matchesNull(v___x_4813_, v___x_4763_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v_env_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_dec(v___x_4813_);
lean_del_object(v___x_2398_);
lean_inc_n(v_stx_2334_, 2);
v___x_4815_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4816_ = lean_st_ref_get(v_a_2340_);
v_env_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc_ref(v_env_4817_);
lean_dec(v___x_4816_);
v___x_4818_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4819_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4818_, v_env_4817_, v___x_4815_);
v___x_4820_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4821_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4819_, v___x_4820_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4819_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4852_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4824_ = v___x_4821_;
v_isShared_4825_ = v_isSharedCheck_4852_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4821_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4852_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v_fst_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4850_; 
v_fst_4826_ = lean_ctor_get(v_a_4822_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v_a_4822_);
if (v_isSharedCheck_4850_ == 0)
{
lean_object* v_unused_4851_; 
v_unused_4851_ = lean_ctor_get(v_a_4822_, 1);
lean_dec(v_unused_4851_);
v___x_4828_ = v_a_4822_;
v_isShared_4829_ = v_isSharedCheck_4850_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_fst_4826_);
lean_dec(v_a_4822_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4850_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
if (lean_obj_tag(v_fst_4826_) == 0)
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4833_; 
lean_del_object(v___x_4824_);
v___x_4830_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4831_ = l_Lean_MessageData_ofName(v___x_4815_);
lean_inc_ref(v___x_4831_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set_tag(v___x_4828_, 7);
lean_ctor_set(v___x_4828_, 1, v___x_4831_);
lean_ctor_set(v___x_4828_, 0, v___x_4830_);
v___x_4833_ = v___x_4828_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v___x_4831_);
v___x_4833_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4834_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4833_);
lean_ctor_set(v___x_4835_, 1, v___x_4834_);
v___x_4836_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4837_ = l_Lean_indentD(v___x_4836_);
v___x_4838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4835_);
lean_ctor_set(v___x_4838_, 1, v___x_4837_);
v___x_4839_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
lean_ctor_set(v___x_4841_, 1, v___x_4831_);
v___x_4842_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4841_);
lean_ctor_set(v___x_4843_, 1, v___x_4842_);
v___x_4844_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4843_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4844_;
}
}
else
{
lean_object* v_val_4846_; lean_object* v___x_4848_; 
lean_del_object(v___x_4828_);
lean_dec(v___x_4815_);
lean_dec(v_stx_2334_);
v_val_4846_ = lean_ctor_get(v_fst_4826_, 0);
lean_inc(v_val_4846_);
lean_dec_ref_known(v_fst_4826_, 1);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v_val_4846_);
v___x_4848_ = v___x_4824_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_val_4846_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v___x_4815_);
lean_dec(v_stx_2334_);
v_a_4853_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4821_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4821_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
if (v___x_2601_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4861_ = l_Lean_Syntax_getArg(v___x_4813_, v___x_4713_);
lean_dec(v___x_4813_);
v___x_4862_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4863_ = l_Lean_Syntax_isOfKind(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v_env_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
lean_del_object(v___x_2398_);
lean_inc_n(v_stx_2334_, 2);
v___x_4864_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4865_ = lean_st_ref_get(v_a_2340_);
v_env_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc_ref(v_env_4866_);
lean_dec(v___x_4865_);
v___x_4867_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4868_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4867_, v_env_4866_, v___x_4864_);
v___x_4869_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4870_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4868_, v___x_4869_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4868_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4901_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4901_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4901_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v_fst_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4899_; 
v_fst_4875_ = lean_ctor_get(v_a_4871_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_a_4871_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v_a_4871_, 1);
lean_dec(v_unused_4900_);
v___x_4877_ = v_a_4871_;
v_isShared_4878_ = v_isSharedCheck_4899_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_fst_4875_);
lean_dec(v_a_4871_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4899_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
if (lean_obj_tag(v_fst_4875_) == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
lean_del_object(v___x_4873_);
v___x_4879_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4880_ = l_Lean_MessageData_ofName(v___x_4864_);
lean_inc_ref(v___x_4880_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set_tag(v___x_4877_, 7);
lean_ctor_set(v___x_4877_, 1, v___x_4880_);
lean_ctor_set(v___x_4877_, 0, v___x_4879_);
v___x_4882_ = v___x_4877_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4883_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4886_ = l_Lean_indentD(v___x_4885_);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4884_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4887_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
lean_ctor_set(v___x_4890_, 1, v___x_4880_);
v___x_4891_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4892_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4893_;
}
}
else
{
lean_object* v_val_4895_; lean_object* v___x_4897_; 
lean_del_object(v___x_4877_);
lean_dec(v___x_4864_);
lean_dec(v_stx_2334_);
v_val_4895_ = lean_ctor_get(v_fst_4875_, 0);
lean_inc(v_val_4895_);
lean_dec_ref_known(v_fst_4875_, 1);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v_val_4895_);
v___x_4897_ = v___x_4873_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_val_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec(v___x_4864_);
lean_dec(v_stx_2334_);
v_a_4902_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4870_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4870_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2400_;
}
}
else
{
lean_dec(v___x_4813_);
lean_dec(v_stx_2334_);
goto v___jp_2400_;
}
}
}
}
}
v___jp_2604_:
{
if (v___x_2603_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2611_ = lean_unsigned_to_nat(2u);
v___x_2612_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2611_);
v___x_2613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2614_ = l_Lean_Syntax_isOfKind(v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_env_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2615_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2616_ = lean_st_ref_get(v___y_2610_);
v_env_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_env_2617_);
lean_dec(v___x_2616_);
v___x_2618_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2619_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2618_, v_env_2617_, v___x_2615_);
v___x_2620_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2621_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2619_, v___x_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___x_2619_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2652_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2652_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2652_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_fst_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2650_; 
v_fst_2626_ = lean_ctor_get(v_a_2622_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v_a_2622_, 1);
lean_dec(v_unused_2651_);
v___x_2628_ = v_a_2622_;
v_isShared_2629_ = v_isSharedCheck_2650_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_fst_2626_);
lean_dec(v_a_2622_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2650_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
if (lean_obj_tag(v_fst_2626_) == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_del_object(v___x_2624_);
v___x_2630_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2631_ = l_Lean_MessageData_ofName(v___x_2615_);
lean_inc_ref(v___x_2631_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 7);
lean_ctor_set(v___x_2628_, 1, v___x_2631_);
lean_ctor_set(v___x_2628_, 0, v___x_2630_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2637_ = l_Lean_indentD(v___x_2636_);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2635_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v___x_2631_);
v___x_2642_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2643_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2644_;
}
}
else
{
lean_object* v_val_2646_; lean_object* v___x_2648_; 
lean_del_object(v___x_2628_);
lean_dec(v___x_2615_);
lean_dec(v_stx_2334_);
v_val_2646_ = lean_ctor_get(v_fst_2626_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v_fst_2626_, 1);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v_val_2646_);
v___x_2648_ = v___x_2624_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_val_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v___x_2615_);
lean_dec(v_stx_2334_);
v_a_2653_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2621_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2621_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
v___y_2361_ = v___y_2607_;
v___y_2362_ = v___y_2608_;
v___y_2363_ = v___y_2610_;
v___y_2364_ = v___y_2606_;
v___y_2365_ = v___y_2605_;
v___y_2366_ = v___y_2609_;
goto v___jp_2360_;
}
}
else
{
v___y_2361_ = v___y_2607_;
v___y_2362_ = v___y_2608_;
v___y_2363_ = v___y_2610_;
v___y_2364_ = v___y_2606_;
v___y_2365_ = v___y_2605_;
v___y_2366_ = v___y_2609_;
goto v___jp_2360_;
}
}
}
else
{
lean_del_object(v___x_2398_);
if (v___x_2548_ == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4910_ = lean_unsigned_to_nat(1u);
v___x_4911_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4910_);
v___x_4912_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_4913_ = l_Lean_Syntax_isOfKind(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v_env_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4914_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4915_ = lean_st_ref_get(v_a_2340_);
v_env_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc_ref(v_env_4916_);
lean_dec(v___x_4915_);
v___x_4917_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4918_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4917_, v_env_4916_, v___x_4914_);
v___x_4919_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4920_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4918_, v___x_4919_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4918_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4951_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4923_ = v___x_4920_;
v_isShared_4924_ = v_isSharedCheck_4951_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4920_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4951_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v_fst_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4949_; 
v_fst_4925_ = lean_ctor_get(v_a_4921_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v_a_4921_);
if (v_isSharedCheck_4949_ == 0)
{
lean_object* v_unused_4950_; 
v_unused_4950_ = lean_ctor_get(v_a_4921_, 1);
lean_dec(v_unused_4950_);
v___x_4927_ = v_a_4921_;
v_isShared_4928_ = v_isSharedCheck_4949_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_fst_4925_);
lean_dec(v_a_4921_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4949_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
if (lean_obj_tag(v_fst_4925_) == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
lean_del_object(v___x_4923_);
v___x_4929_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4930_ = l_Lean_MessageData_ofName(v___x_4914_);
lean_inc_ref(v___x_4930_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set_tag(v___x_4927_, 7);
lean_ctor_set(v___x_4927_, 1, v___x_4930_);
lean_ctor_set(v___x_4927_, 0, v___x_4929_);
v___x_4932_ = v___x_4927_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4944_, 1, v___x_4930_);
v___x_4932_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4933_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4932_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4936_ = l_Lean_indentD(v___x_4935_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4934_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v___x_4930_);
v___x_4941_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4942_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4943_;
}
}
else
{
lean_object* v_val_4945_; lean_object* v___x_4947_; 
lean_del_object(v___x_4927_);
lean_dec(v___x_4914_);
lean_dec(v_stx_2334_);
v_val_4945_ = lean_ctor_get(v_fst_4925_, 0);
lean_inc(v_val_4945_);
lean_dec_ref_known(v_fst_4925_, 1);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v_val_4945_);
v___x_4947_ = v___x_4923_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_val_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v___x_4914_);
lean_dec(v_stx_2334_);
v_a_4952_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4920_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4920_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
goto v___jp_2549_;
}
}
else
{
goto v___jp_2549_;
}
}
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
lean_del_object(v___x_2398_);
v___x_4960_ = lean_unsigned_to_nat(1u);
v___x_4961_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_4960_);
v___x_4962_ = l_Lean_Syntax_isNone(v___x_4961_);
if (v___x_4962_ == 0)
{
uint8_t v___x_4963_; 
v___x_4963_ = l_Lean_Syntax_matchesNull(v___x_4961_, v___x_4960_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v_env_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
lean_inc_n(v_stx_2334_, 2);
v___x_4964_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_4965_ = lean_st_ref_get(v_a_2340_);
v_env_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc_ref(v_env_4966_);
lean_dec(v___x_4965_);
v___x_4967_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4968_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4967_, v_env_4966_, v___x_4964_);
v___x_4969_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4970_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_4968_, v___x_4969_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_4968_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5001_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_5001_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5001_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v_fst_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4999_; 
v_fst_4975_ = lean_ctor_get(v_a_4971_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_a_4971_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; 
v_unused_5000_ = lean_ctor_get(v_a_4971_, 1);
lean_dec(v_unused_5000_);
v___x_4977_ = v_a_4971_;
v_isShared_4978_ = v_isSharedCheck_4999_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_fst_4975_);
lean_dec(v_a_4971_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4999_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
if (lean_obj_tag(v_fst_4975_) == 0)
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4982_; 
lean_del_object(v___x_4973_);
v___x_4979_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4980_ = l_Lean_MessageData_ofName(v___x_4964_);
lean_inc_ref(v___x_4980_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set_tag(v___x_4977_, 7);
lean_ctor_set(v___x_4977_, 1, v___x_4980_);
lean_ctor_set(v___x_4977_, 0, v___x_4979_);
v___x_4982_ = v___x_4977_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4979_);
lean_ctor_set(v_reuseFailAlloc_4994_, 1, v___x_4980_);
v___x_4982_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4983_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_4986_ = l_Lean_indentD(v___x_4985_);
v___x_4987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4984_);
lean_ctor_set(v___x_4987_, 1, v___x_4986_);
v___x_4988_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4987_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v___x_4980_);
v___x_4991_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4992_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_4993_;
}
}
else
{
lean_object* v_val_4995_; lean_object* v___x_4997_; 
lean_del_object(v___x_4977_);
lean_dec(v___x_4964_);
lean_dec(v_stx_2334_);
v_val_4995_ = lean_ctor_get(v_fst_4975_, 0);
lean_inc(v_val_4995_);
lean_dec_ref_known(v_fst_4975_, 1);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 0, v_val_4995_);
v___x_4997_ = v___x_4973_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_val_4995_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v___x_4964_);
lean_dec(v_stx_2334_);
v_a_5002_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4970_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4970_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
else
{
v___y_2491_ = v_a_2335_;
v___y_2492_ = v_a_2336_;
v___y_2493_ = v_a_2337_;
v___y_2494_ = v_a_2338_;
v___y_2495_ = v_a_2339_;
v___y_2496_ = v_a_2340_;
goto v___jp_2490_;
}
}
else
{
lean_dec(v___x_4961_);
v___y_2491_ = v_a_2335_;
v___y_2492_ = v_a_2336_;
v___y_2493_ = v_a_2337_;
v___y_2494_ = v_a_2338_;
v___y_2495_ = v_a_2339_;
v___y_2496_ = v_a_2340_;
goto v___jp_2490_;
}
}
v___jp_2549_:
{
if (v___x_2548_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2550_ = lean_unsigned_to_nat(2u);
v___x_2551_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2553_ = l_Lean_Syntax_isOfKind(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v_env_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2554_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2555_ = lean_st_ref_get(v_a_2340_);
v_env_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2556_);
lean_dec(v___x_2555_);
v___x_2557_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2558_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2557_, v_env_2556_, v___x_2554_);
v___x_2559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2560_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2558_, v___x_2559_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2591_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2591_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2591_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_fst_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2589_; 
v_fst_2565_ = lean_ctor_get(v_a_2561_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v_a_2561_, 1);
lean_dec(v_unused_2590_);
v___x_2567_ = v_a_2561_;
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_fst_2565_);
lean_dec(v_a_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
if (lean_obj_tag(v_fst_2565_) == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_del_object(v___x_2563_);
v___x_2569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2570_ = l_Lean_MessageData_ofName(v___x_2554_);
lean_inc_ref(v___x_2570_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 7);
lean_ctor_set(v___x_2567_, 1, v___x_2570_);
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2573_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2576_ = l_Lean_indentD(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2574_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2570_);
v___x_2581_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2582_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2583_;
}
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2587_; 
lean_del_object(v___x_2567_);
lean_dec(v___x_2554_);
lean_dec(v_stx_2334_);
v_val_2585_ = lean_ctor_get(v_fst_2565_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v_fst_2565_, 1);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v_val_2585_);
v___x_2587_ = v___x_2563_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_val_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v___x_2554_);
lean_dec(v_stx_2334_);
v_a_2592_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2560_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2560_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2405_;
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2405_;
}
}
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
lean_del_object(v___x_2398_);
v___x_5010_ = lean_unsigned_to_nat(1u);
v___x_5011_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_5010_);
lean_dec(v_stx_2334_);
v___x_5012_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5011_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_5012_;
}
v___jp_2433_:
{
if (v___x_2432_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2440_ = lean_unsigned_to_nat(3u);
v___x_2441_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2440_);
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2443_ = l_Lean_Syntax_isOfKind(v___x_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_env_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2444_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2445_ = lean_st_ref_get(v___y_2434_);
v_env_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc_ref(v_env_2446_);
lean_dec(v___x_2445_);
v___x_2447_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2448_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2447_, v_env_2446_, v___x_2444_);
v___x_2449_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2450_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2448_, v___x_2449_, v___y_2439_, v___y_2437_, v___y_2438_, v___y_2435_, v___y_2436_, v___y_2434_);
lean_dec(v___x_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2481_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_fst_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2479_; 
v_fst_2455_ = lean_ctor_get(v_a_2451_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_a_2451_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v_a_2451_, 1);
lean_dec(v_unused_2480_);
v___x_2457_ = v_a_2451_;
v_isShared_2458_ = v_isSharedCheck_2479_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_fst_2455_);
lean_dec(v_a_2451_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2479_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
if (lean_obj_tag(v_fst_2455_) == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_del_object(v___x_2453_);
v___x_2459_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2460_ = l_Lean_MessageData_ofName(v___x_2444_);
lean_inc_ref(v___x_2460_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 7);
lean_ctor_set(v___x_2457_, 1, v___x_2460_);
lean_ctor_set(v___x_2457_, 0, v___x_2459_);
v___x_2462_ = v___x_2457_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2463_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2466_ = l_Lean_indentD(v___x_2465_);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2464_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2460_);
v___x_2471_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2472_, v___y_2439_, v___y_2437_, v___y_2438_, v___y_2435_, v___y_2436_, v___y_2434_);
return v___x_2473_;
}
}
else
{
lean_object* v_val_2475_; lean_object* v___x_2477_; 
lean_del_object(v___x_2457_);
lean_dec(v___x_2444_);
lean_dec(v_stx_2334_);
v_val_2475_ = lean_ctor_get(v_fst_2455_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v_fst_2455_, 1);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_val_2475_);
v___x_2477_ = v___x_2453_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_val_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v___x_2444_);
lean_dec(v_stx_2334_);
v_a_2482_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2450_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2450_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2381_;
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_2381_;
}
}
v___jp_2490_:
{
if (v___x_2432_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2497_ = lean_unsigned_to_nat(2u);
v___x_2498_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2500_ = l_Lean_Syntax_isOfKind(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_env_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_inc_n(v_stx_2334_, 2);
v___x_2501_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_2502_ = lean_st_ref_get(v___y_2496_);
v_env_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc_ref(v_env_2503_);
lean_dec(v___x_2502_);
v___x_2504_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2505_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2504_, v_env_2503_, v___x_2501_);
v___x_2506_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2507_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_2505_, v___x_2506_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___x_2505_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2538_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2538_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2538_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_fst_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2536_; 
v_fst_2512_ = lean_ctor_get(v_a_2508_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; 
v_unused_2537_ = lean_ctor_get(v_a_2508_, 1);
lean_dec(v_unused_2537_);
v___x_2514_ = v_a_2508_;
v_isShared_2515_ = v_isSharedCheck_2536_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_fst_2512_);
lean_dec(v_a_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2536_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
if (lean_obj_tag(v_fst_2512_) == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_del_object(v___x_2510_);
v___x_2516_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2517_ = l_Lean_MessageData_ofName(v___x_2501_);
lean_inc_ref(v___x_2517_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 7);
lean_ctor_set(v___x_2514_, 1, v___x_2517_);
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2519_ = v___x_2514_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2520_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_2523_ = l_Lean_indentD(v___x_2522_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2521_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2517_);
v___x_2528_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2529_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v___x_2530_;
}
}
else
{
lean_object* v_val_2532_; lean_object* v___x_2534_; 
lean_del_object(v___x_2514_);
lean_dec(v___x_2501_);
lean_dec(v_stx_2334_);
v_val_2532_ = lean_ctor_get(v_fst_2512_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v_fst_2512_, 1);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_val_2532_);
v___x_2534_ = v___x_2510_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_val_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v___x_2501_);
lean_dec(v_stx_2334_);
v_a_2539_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2507_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2507_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
v___y_2434_ = v___y_2496_;
v___y_2435_ = v___y_2494_;
v___y_2436_ = v___y_2495_;
v___y_2437_ = v___y_2492_;
v___y_2438_ = v___y_2493_;
v___y_2439_ = v___y_2491_;
goto v___jp_2433_;
}
}
else
{
v___y_2434_ = v___y_2496_;
v___y_2435_ = v___y_2494_;
v___y_2436_ = v___y_2495_;
v___y_2437_ = v___y_2492_;
v___y_2438_ = v___y_2493_;
v___y_2439_ = v___y_2491_;
goto v___jp_2433_;
}
}
}
else
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
lean_del_object(v___x_2398_);
v___x_5013_ = lean_unsigned_to_nat(0u);
v___x_5014_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_5013_);
lean_dec(v_stx_2334_);
v___x_5015_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5014_);
if (lean_obj_tag(v___x_5015_) == 1)
{
lean_object* v_val_5016_; lean_object* v_snd_5017_; lean_object* v_body_5018_; lean_object* v___x_5019_; 
v_val_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_val_5016_);
lean_dec_ref_known(v___x_5015_, 1);
v_snd_5017_ = lean_ctor_get(v_val_5016_, 1);
lean_inc(v_snd_5017_);
lean_dec(v_val_5016_);
v_body_5018_ = lean_ctor_get(v_snd_5017_, 1);
lean_inc(v_body_5018_);
lean_dec(v_snd_5017_);
v___x_5019_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5018_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5040_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5040_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5040_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
uint8_t v_breaks_5024_; uint8_t v_continues_5025_; uint8_t v_returnsEarly_5026_; lean_object* v_reassigns_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5038_; 
v_breaks_5024_ = lean_ctor_get_uint8(v_a_5020_, sizeof(void*)*2);
v_continues_5025_ = lean_ctor_get_uint8(v_a_5020_, sizeof(void*)*2 + 1);
v_returnsEarly_5026_ = lean_ctor_get_uint8(v_a_5020_, sizeof(void*)*2 + 2);
v_reassigns_5027_ = lean_ctor_get(v_a_5020_, 1);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_a_5020_);
if (v_isSharedCheck_5038_ == 0)
{
lean_object* v_unused_5039_; 
v_unused_5039_ = lean_ctor_get(v_a_5020_, 0);
lean_dec(v_unused_5039_);
v___x_5029_ = v_a_5020_;
v_isShared_5030_ = v_isSharedCheck_5038_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_reassigns_5027_);
lean_dec(v_a_5020_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5038_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5031_ = lean_unsigned_to_nat(1u);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5031_);
v___x_5033_ = v___x_5029_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5031_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v_reassigns_5027_);
lean_ctor_set_uint8(v_reuseFailAlloc_5037_, sizeof(void*)*2, v_breaks_5024_);
lean_ctor_set_uint8(v_reuseFailAlloc_5037_, sizeof(void*)*2 + 1, v_continues_5025_);
lean_ctor_set_uint8(v_reuseFailAlloc_5037_, sizeof(void*)*2 + 2, v_returnsEarly_5026_);
v___x_5033_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5035_; 
lean_ctor_set_uint8(v___x_5033_, sizeof(void*)*2 + 3, v___x_2428_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5033_);
v___x_5035_ = v___x_5022_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5033_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
}
else
{
return v___x_5019_;
}
}
else
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec(v___x_5015_);
v___x_5041_ = lean_unsigned_to_nat(1u);
v___x_5042_ = l_Lean_NameSet_empty;
v___x_5043_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5043_, 0, v___x_5041_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*2, v___x_2428_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*2 + 1, v___x_2428_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*2 + 2, v___x_2428_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*2 + 3, v___x_2428_);
v___x_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
}
}
else
{
lean_object* v___x_5045_; lean_object* v___x_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
lean_del_object(v___x_2398_);
v___x_5045_ = lean_unsigned_to_nat(0u);
v___x_5050_ = lean_unsigned_to_nat(1u);
v___x_5051_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_5050_);
v___x_5052_ = l_Lean_Syntax_isNone(v___x_5051_);
if (v___x_5052_ == 0)
{
uint8_t v___x_5053_; 
v___x_5053_ = l_Lean_Syntax_matchesNull(v___x_5051_, v___x_5050_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v_env_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_inc_n(v_stx_2334_, 2);
v___x_5054_ = l_Lean_Syntax_getKind(v_stx_2334_);
v___x_5055_ = lean_st_ref_get(v_a_2340_);
v_env_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc_ref(v_env_5056_);
lean_dec(v___x_5055_);
v___x_5057_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5058_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5057_, v_env_5056_, v___x_5054_);
v___x_5059_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5060_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2334_, v___x_5058_, v___x_5059_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v___x_5058_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5091_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5091_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5091_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v_fst_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5089_; 
v_fst_5065_ = lean_ctor_get(v_a_5061_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v_a_5061_);
if (v_isSharedCheck_5089_ == 0)
{
lean_object* v_unused_5090_; 
v_unused_5090_ = lean_ctor_get(v_a_5061_, 1);
lean_dec(v_unused_5090_);
v___x_5067_ = v_a_5061_;
v_isShared_5068_ = v_isSharedCheck_5089_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_fst_5065_);
lean_dec(v_a_5061_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5089_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
if (lean_obj_tag(v_fst_5065_) == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5072_; 
lean_del_object(v___x_5063_);
v___x_5069_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5070_ = l_Lean_MessageData_ofName(v___x_5054_);
lean_inc_ref(v___x_5070_);
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 7);
lean_ctor_set(v___x_5067_, 1, v___x_5070_);
lean_ctor_set(v___x_5067_, 0, v___x_5069_);
v___x_5072_ = v___x_5067_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5069_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5073_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = l_Lean_MessageData_ofSyntax(v_stx_2334_);
v___x_5076_ = l_Lean_indentD(v___x_5075_);
v___x_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5074_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
lean_ctor_set(v___x_5080_, 1, v___x_5070_);
v___x_5081_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5080_);
lean_ctor_set(v___x_5082_, 1, v___x_5081_);
v___x_5083_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5082_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_5083_;
}
}
else
{
lean_object* v_val_5085_; lean_object* v___x_5087_; 
lean_del_object(v___x_5067_);
lean_dec(v___x_5054_);
lean_dec(v_stx_2334_);
v_val_5085_ = lean_ctor_get(v_fst_5065_, 0);
lean_inc(v_val_5085_);
lean_dec_ref_known(v_fst_5065_, 1);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v_val_5085_);
v___x_5087_ = v___x_5063_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_val_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec(v___x_5054_);
lean_dec(v_stx_2334_);
v_a_5092_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5060_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5060_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_dec(v_stx_2334_);
goto v___jp_5046_;
}
}
else
{
lean_dec(v___x_5051_);
lean_dec(v_stx_2334_);
goto v___jp_5046_;
}
v___jp_5046_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = l_Lean_NameSet_empty;
v___x_5048_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5048_, 0, v___x_5045_);
lean_ctor_set(v___x_5048_, 1, v___x_5047_);
lean_ctor_set_uint8(v___x_5048_, sizeof(void*)*2, v___x_2426_);
lean_ctor_set_uint8(v___x_5048_, sizeof(void*)*2 + 1, v___x_2426_);
lean_ctor_set_uint8(v___x_5048_, sizeof(void*)*2 + 2, v___x_2424_);
lean_ctor_set_uint8(v___x_5048_, sizeof(void*)*2 + 3, v___x_2424_);
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5048_);
return v___x_5049_;
}
}
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
lean_del_object(v___x_2398_);
lean_dec(v_stx_2334_);
v___x_5100_ = lean_unsigned_to_nat(0u);
v___x_5101_ = l_Lean_NameSet_empty;
v___x_5102_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5102_, 0, v___x_5100_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*2, v___x_2423_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*2 + 1, v___x_2424_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*2 + 2, v___x_2423_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*2 + 3, v___x_2424_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
lean_del_object(v___x_2398_);
lean_dec(v_stx_2334_);
v___x_5104_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
v___jp_2400_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
v___jp_2405_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_stx_2334_);
v_a_5107_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_2395_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_2395_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
v___jp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2343_, v_bodyInfo_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
v___jp_2347_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2353_);
v___x_2359_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2356_, v___x_2357_, v___x_2358_, v___y_2355_, v___y_2352_, v___y_2351_, v___y_2350_, v___y_2349_, v___y_2354_, v___y_2348_);
return v___x_2359_;
}
v___jp_2360_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2367_ = lean_unsigned_to_nat(7u);
v___x_2368_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2367_);
v___x_2369_ = lean_unsigned_to_nat(8u);
v___x_2370_ = l_Lean_Syntax_getArg(v_stx_2334_, v___x_2369_);
lean_dec(v_stx_2334_);
v___x_2371_ = l_Lean_Syntax_getOptional_x3f(v___x_2370_);
lean_dec(v___x_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_box(0);
v___y_2348_ = v___y_2363_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___y_2361_;
v___y_2351_ = v___y_2364_;
v___y_2352_ = v___y_2365_;
v___y_2353_ = v___x_2368_;
v___y_2354_ = v___y_2366_;
v___y_2355_ = v___x_2372_;
goto v___jp_2347_;
}
else
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_val_2373_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_val_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
v___y_2348_ = v___y_2363_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___y_2361_;
v___y_2351_ = v___y_2364_;
v___y_2352_ = v___y_2365_;
v___y_2353_ = v___x_2368_;
v___y_2354_ = v___y_2366_;
v___y_2355_ = v___x_2378_;
goto v___jp_2347_;
}
}
}
}
v___jp_2381_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
v___jp_2384_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
v___jp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2388_, v_bodyInfo_2389_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5115_, size_t v_sz_5116_, size_t v_i_5117_, lean_object* v_b_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
uint8_t v___x_5126_; 
v___x_5126_ = lean_usize_dec_lt(v_i_5117_, v_sz_5116_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; 
v___x_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5127_, 0, v_b_5118_);
return v___x_5127_;
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; 
v_a_5128_ = lean_array_uget_borrowed(v_as_5115_, v_i_5117_);
lean_inc(v_a_5128_);
v___x_5129_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5128_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; size_t v___x_5132_; size_t v___x_5133_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v___x_5131_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5118_, v_a_5130_);
v___x_5132_ = ((size_t)1ULL);
v___x_5133_ = lean_usize_add(v_i_5117_, v___x_5132_);
v_i_5117_ = v___x_5133_;
v_b_5118_ = v___x_5131_;
goto _start;
}
else
{
lean_dec_ref(v_b_5118_);
return v___x_5129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_){
_start:
{
lean_object* v_info_5143_; lean_object* v___x_5144_; size_t v_sz_5145_; size_t v___x_5146_; lean_object* v___x_5147_; 
v_info_5143_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5144_ = l_Lean_Parser_Term_getDoElems(v_stx_5135_);
v_sz_5145_ = lean_array_size(v___x_5144_);
v___x_5146_ = ((size_t)0ULL);
v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5144_, v_sz_5145_, v___x_5146_, v_info_5143_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
lean_dec_ref(v___x_5144_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec(v_a_5161_);
lean_dec_ref(v_a_5160_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5166_, lean_object* v_sz_5167_, lean_object* v_i_5168_, lean_object* v_b_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
size_t v_sz_boxed_5177_; size_t v_i_boxed_5178_; lean_object* v_res_5179_; 
v_sz_boxed_5177_ = lean_unbox_usize(v_sz_5167_);
lean_dec(v_sz_5167_);
v_i_boxed_5178_ = lean_unbox_usize(v_i_5168_);
lean_dec(v_i_5168_);
v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5166_, v_sz_boxed_5177_, v_i_boxed_5178_, v_b_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec_ref(v_as_5166_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5180_, lean_object* v_sz_5181_, lean_object* v_i_5182_, lean_object* v_b_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
size_t v_sz_boxed_5191_; size_t v_i_boxed_5192_; lean_object* v_res_5193_; 
v_sz_boxed_5191_ = lean_unbox_usize(v_sz_5181_);
lean_dec(v_sz_5181_);
v_i_boxed_5192_ = lean_unbox_usize(v_i_5182_);
lean_dec(v_i_5182_);
v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5180_, v_sz_boxed_5191_, v_i_boxed_5192_, v_b_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec_ref(v_as_5180_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5194_, lean_object* v_as_5195_, lean_object* v_sz_5196_, lean_object* v_i_5197_, lean_object* v_b_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
uint8_t v___x_178461__boxed_5206_; size_t v_sz_boxed_5207_; size_t v_i_boxed_5208_; lean_object* v_res_5209_; 
v___x_178461__boxed_5206_ = lean_unbox(v___x_5194_);
v_sz_boxed_5207_ = lean_unbox_usize(v_sz_5196_);
lean_dec(v_sz_5196_);
v_i_boxed_5208_ = lean_unbox_usize(v_i_5197_);
lean_dec(v_i_5197_);
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_178461__boxed_5206_, v_as_5195_, v_sz_boxed_5207_, v_i_boxed_5208_, v_b_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_as_5195_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5210_, lean_object* v_as_5211_, lean_object* v_sz_5212_, lean_object* v_i_5213_, lean_object* v_b_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
uint8_t v___x_178508__boxed_5222_; size_t v_sz_boxed_5223_; size_t v_i_boxed_5224_; lean_object* v_res_5225_; 
v___x_178508__boxed_5222_ = lean_unbox(v___x_5210_);
v_sz_boxed_5223_ = lean_unbox_usize(v_sz_5212_);
lean_dec(v_sz_5212_);
v_i_boxed_5224_ = lean_unbox_usize(v_i_5213_);
lean_dec(v_i_5213_);
v_res_5225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_178508__boxed_5222_, v_as_5211_, v_sz_boxed_5223_, v_i_boxed_5224_, v_b_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec_ref(v_as_5211_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5226_, lean_object* v_rhs_x3f_5227_, lean_object* v_otherwise_x3f_5228_, lean_object* v_body_x3f_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5226_, v_rhs_x3f_5227_, v_otherwise_x3f_5228_, v_body_x3f_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
lean_dec_ref(v_a_5232_);
lean_dec(v_a_5231_);
lean_dec_ref(v_a_5230_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5238_, lean_object* v_sz_5239_, lean_object* v_i_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
size_t v_sz_boxed_5249_; size_t v_i_boxed_5250_; lean_object* v_res_5251_; 
v_sz_boxed_5249_ = lean_unbox_usize(v_sz_5239_);
lean_dec(v_sz_5239_);
v_i_boxed_5250_ = lean_unbox_usize(v_i_5240_);
lean_dec(v_i_5240_);
v_res_5251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5238_, v_sz_boxed_5249_, v_i_boxed_5250_, v_b_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec_ref(v_as_5238_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5252_, lean_object* v_decl_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
uint8_t v_reassignment_boxed_5261_; lean_object* v_res_5262_; 
v_reassignment_boxed_5261_ = lean_unbox(v_reassignment_5252_);
v_res_5262_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5261_, v_decl_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
v___x_5280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5290_, lean_object* v_ref_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5291_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5300_, lean_object* v_ref_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5300_, v_ref_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5310_, lean_object* v_x_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5320_, lean_object* v_x_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5320_, v_x_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec(v___y_5325_);
lean_dec_ref(v___y_5324_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5330_, lean_object* v_as_5331_, lean_object* v_as_x27_5332_, lean_object* v_b_5333_, lean_object* v_a_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v___x_5342_; 
v___x_5342_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5330_, v_as_x27_5332_, v_b_5333_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5343_, lean_object* v_as_5344_, lean_object* v_as_x27_5345_, lean_object* v_b_5346_, lean_object* v_a_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5343_, v_as_5344_, v_as_x27_5345_, v_b_5346_, v_a_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v_as_x27_5345_);
lean_dec(v_as_5344_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5356_, lean_object* v_msg_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5366_, lean_object* v_msg_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5366_, v_msg_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5376_, lean_object* v_msg_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5376_, v_msg_5377_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5386_, lean_object* v_msg_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5386_, v_msg_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5396_, lean_object* v_as_x27_5397_, lean_object* v_b_5398_, lean_object* v_a_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
lean_object* v___x_5407_; 
v___x_5407_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5397_, v_b_5398_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5408_, lean_object* v_as_x27_5409_, lean_object* v_b_5410_, lean_object* v_a_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5408_, v_as_x27_5409_, v_b_5410_, v_a_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v___y_5412_);
lean_dec(v_as_x27_5409_);
lean_dec(v_as_5408_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5420_, lean_object* v_ref_5421_, lean_object* v_msg_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v___x_5430_; 
v___x_5430_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5421_, v_msg_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5431_, lean_object* v_ref_5432_, lean_object* v_msg_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5431_, v_ref_5432_, v_msg_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v_ref_5432_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5442_, lean_object* v_macroStack_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v___x_5451_; 
v___x_5451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5442_, v_macroStack_5443_, v___y_5448_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5452_, lean_object* v_macroStack_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5452_, v_macroStack_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5462_, lean_object* v_m_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5463_, v_a_5464_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5466_, lean_object* v_m_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5466_, v_m_5467_, v_a_5468_);
lean_dec(v_a_5468_);
lean_dec_ref(v_m_5467_);
return v_res_5469_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5470_, lean_object* v_x_5471_, lean_object* v_x_5472_){
_start:
{
uint8_t v___x_5473_; 
v___x_5473_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5471_, v_x_5472_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5474_, lean_object* v_x_5475_, lean_object* v_x_5476_){
_start:
{
uint8_t v_res_5477_; lean_object* v_r_5478_; 
v_res_5477_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5474_, v_x_5475_, v_x_5476_);
lean_dec_ref(v_x_5476_);
lean_dec_ref(v_x_5475_);
v_r_5478_ = lean_box(v_res_5477_);
return v_r_5478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5479_, lean_object* v_a_5480_, lean_object* v_x_5481_){
_start:
{
lean_object* v___x_5482_; 
v___x_5482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5480_, v_x_5481_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5483_, lean_object* v_a_5484_, lean_object* v_x_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5483_, v_a_5484_, v_x_5485_);
lean_dec(v_x_5485_);
lean_dec(v_a_5484_);
return v_res_5486_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5487_, lean_object* v_x_5488_, size_t v_x_5489_, lean_object* v_x_5490_){
_start:
{
uint8_t v___x_5491_; 
v___x_5491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5488_, v_x_5489_, v_x_5490_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5492_, lean_object* v_x_5493_, lean_object* v_x_5494_, lean_object* v_x_5495_){
_start:
{
size_t v_x_185647__boxed_5496_; uint8_t v_res_5497_; lean_object* v_r_5498_; 
v_x_185647__boxed_5496_ = lean_unbox_usize(v_x_5494_);
lean_dec(v_x_5494_);
v_res_5497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5492_, v_x_5493_, v_x_185647__boxed_5496_, v_x_5495_);
lean_dec_ref(v_x_5495_);
lean_dec_ref(v_x_5493_);
v_r_5498_ = lean_box(v_res_5497_);
return v_r_5498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5499_, lean_object* v_keys_5500_, lean_object* v_vals_5501_, lean_object* v_heq_5502_, lean_object* v_i_5503_, lean_object* v_k_5504_){
_start:
{
uint8_t v___x_5505_; 
v___x_5505_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5500_, v_i_5503_, v_k_5504_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5506_, lean_object* v_keys_5507_, lean_object* v_vals_5508_, lean_object* v_heq_5509_, lean_object* v_i_5510_, lean_object* v_k_5511_){
_start:
{
uint8_t v_res_5512_; lean_object* v_r_5513_; 
v_res_5512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5506_, v_keys_5507_, v_vals_5508_, v_heq_5509_, v_i_5510_, v_k_5511_);
lean_dec_ref(v_k_5511_);
lean_dec_ref(v_vals_5508_);
lean_dec_ref(v_keys_5507_);
v_r_5513_ = lean_box(v_res_5512_);
return v_r_5513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_){
_start:
{
lean_object* v___x_5522_; 
v___x_5522_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_);
return v___x_5522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
lean_dec(v_a_5527_);
lean_dec_ref(v_a_5526_);
lean_dec(v_a_5525_);
lean_dec_ref(v_a_5524_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_){
_start:
{
lean_object* v___x_5540_; 
v___x_5540_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5532_, v_a_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_);
return v___x_5540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_);
lean_dec(v_a_5547_);
lean_dec_ref(v_a_5546_);
lean_dec(v_a_5545_);
lean_dec_ref(v_a_5544_);
lean_dec(v_a_5543_);
lean_dec_ref(v_a_5542_);
return v_res_5549_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Do_instInhabitedControlInfo_default = _init_l_Lean_Elab_Do_instInhabitedControlInfo_default();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo_default);
l_Lean_Elab_Do_instInhabitedControlInfo = _init_l_Lean_Elab_Do_instInhabitedControlInfo();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo);
l_Lean_Elab_Do_ControlInfo_pure = _init_l_Lean_Elab_Do_ControlInfo_pure();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_pure);
l_Lean_Elab_Do_ControlInfo_empty = _init_l_Lean_Elab_Do_ControlInfo_empty();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_empty);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_InferControlInfo(builtin);
}
#ifdef __cplusplus
}
#endif
