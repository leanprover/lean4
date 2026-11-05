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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; uint8_t v___y_28_; uint8_t v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_26_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_27_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_27_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_29_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_28_);
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
v___y_25_ = v___y_36_;
v___y_26_ = v_reassigns_41_;
v___y_27_ = v_numRegularExits_39_;
v___y_28_ = v___y_38_;
v___y_29_ = v___y_37_;
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
v___y_25_ = v___y_36_;
v___y_26_ = v_reassigns_43_;
v___y_27_ = v_numRegularExits_42_;
v___y_28_ = v___y_38_;
v___y_29_ = v___y_37_;
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
uint8_t v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; uint8_t v___y_61_; uint8_t v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_60_, v___y_58_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_59_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_57_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_61_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_62_);
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
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v___x_79_;
v___y_60_ = v_reassigns_71_;
v___y_61_ = v___y_74_;
v___y_62_ = v___y_75_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v___x_79_;
v___y_60_ = v_reassigns_71_;
v___y_61_ = v___y_74_;
v___y_62_ = v___y_75_;
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
v___y_73_ = v___y_81_;
v___y_74_ = v___y_82_;
v___y_75_ = v_returnsEarly_83_;
goto v___jp_72_;
}
else
{
v___y_73_ = v___y_81_;
v___y_74_ = v___y_82_;
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
lean_object* v___x_288_; lean_object* v_env_289_; uint8_t v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; lean_object* v_toCold_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = 0;
v_env_291_ = l_Lean_Environment_setRecordingDeps(v_env_289_, v___x_290_);
v___x_292_ = lean_st_ref_get(v___y_284_);
v_toCold_293_ = lean_ctor_get(v___y_285_, 0);
v_mctx_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_292_);
v_lctx_295_ = lean_ctor_get(v___y_283_, 2);
v_options_296_ = lean_ctor_get(v_toCold_293_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_291_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_282_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(1);
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
return v_x_314_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_head_316_ = lean_ctor_get(v_x_315_, 0);
v_tail_317_ = lean_ctor_get(v_x_315_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v_x_315_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_head_316_);
lean_dec(v_x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_before_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_337_; 
v_before_321_ = lean_ctor_get(v_head_316_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_head_316_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_head_316_, 1);
lean_dec(v_unused_338_);
v___x_323_ = v_head_316_;
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_before_321_);
lean_dec(v_head_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 7);
lean_ctor_set(v___x_323_, 1, v___x_325_);
lean_ctor_set(v___x_323_, 0, v_x_314_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_x_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_336_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 7);
lean_ctor_set(v___x_319_, 1, v___x_328_);
lean_ctor_set(v___x_319_, 0, v___x_327_);
v___x_330_ = v___x_319_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_335_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Lean_MessageData_ofSyntax(v_before_321_);
v___x_332_ = l_Lean_indentD(v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v_x_314_ = v___x_333_;
v_x_315_ = v_tail_317_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_340_, lean_object* v_opt_341_){
_start:
{
lean_object* v_name_342_; lean_object* v_defValue_343_; lean_object* v_map_344_; lean_object* v___x_345_; 
v_name_342_ = lean_ctor_get(v_opt_341_, 0);
v_defValue_343_ = lean_ctor_get(v_opt_341_, 1);
v_map_344_ = lean_ctor_get(v_opts_340_, 0);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_344_, v_name_342_);
if (lean_obj_tag(v___x_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = lean_unbox(v_defValue_343_);
return v___x_346_;
}
else
{
lean_object* v_val_347_; 
v_val_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v___x_345_, 1);
if (lean_obj_tag(v_val_347_) == 1)
{
uint8_t v_v_348_; 
v_v_348_ = lean_ctor_get_uint8(v_val_347_, 0);
lean_dec_ref_known(v_val_347_, 0);
return v_v_348_;
}
else
{
uint8_t v___x_349_; 
lean_dec(v_val_347_);
v___x_349_ = lean_unbox(v_defValue_343_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_350_, lean_object* v_opt_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_350_, v_opt_351_);
lean_dec_ref(v_opt_351_);
lean_dec_ref(v_opts_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_358_ = l_Lean_MessageData_ofFormat(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_359_, lean_object* v_macroStack_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_361_);
v___x_364_ = l_Lean_Elab_pp_macroStack;
v___x_365_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v___x_363_, v___x_364_);
lean_dec_ref(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_macroStack_360_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_359_);
return v___x_366_;
}
else
{
if (lean_obj_tag(v_macroStack_360_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_msgData_359_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_after_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_384_; 
v_head_368_ = lean_ctor_get(v_macroStack_360_, 0);
lean_inc(v_head_368_);
v_after_369_ = lean_ctor_get(v_head_368_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_head_368_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_head_368_, 0);
lean_dec(v_unused_385_);
v___x_371_ = v_head_368_;
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_after_369_);
lean_dec(v_head_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 7);
lean_ctor_set(v___x_371_, 1, v___x_373_);
lean_ctor_set(v___x_371_, 0, v_msgData_359_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_msgData_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_msgData_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_MessageData_ofSyntax(v_after_369_);
v___x_379_ = l_Lean_indentD(v___x_378_);
v_msgData_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_380_, 0, v___x_377_);
lean_ctor_set(v_msgData_380_, 1, v___x_379_);
v___x_381_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_380_, v_macroStack_360_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_386_, lean_object* v_macroStack_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_386_, v_macroStack_387_, v___y_388_);
lean_dec_ref(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_ref_399_; lean_object* v_macroStack_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_ref_399_ = lean_ctor_get(v___y_396_, 2);
v_macroStack_400_ = lean_ctor_get(v___y_392_, 1);
v___x_401_ = l_Lean_Elab_getBetterRef(v_ref_399_, v_macroStack_400_);
v___x_402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_391_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
lean_inc(v_macroStack_400_);
v___x_404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_403_, v_macroStack_400_, v___y_396_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_401_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_423_, size_t v_i_424_, size_t v_stop_425_, lean_object* v_b_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_eq(v_i_424_, v_stop_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; size_t v___x_430_; size_t v___x_431_; 
v___x_428_ = lean_array_uget_borrowed(v_as_423_, v_i_424_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_NameSet_insert(v_b_426_, v___x_428_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_424_, v___x_430_);
v_i_424_ = v___x_431_;
v_b_426_ = v___x_429_;
goto _start;
}
else
{
return v_b_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_433_, lean_object* v_i_434_, lean_object* v_stop_435_, lean_object* v_b_436_){
_start:
{
size_t v_i_boxed_437_; size_t v_stop_boxed_438_; lean_object* v_res_439_; 
v_i_boxed_437_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_stop_boxed_438_ = lean_unbox_usize(v_stop_435_);
lean_dec(v_stop_435_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_433_, v_i_boxed_437_, v_stop_boxed_438_, v_b_436_);
lean_dec_ref(v_as_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
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
lean_object* v_v_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget(v_bs_442_, v_i_441_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_445_);
v___x_447_ = l_Lean_TSyntax_getId(v_v_444_);
lean_dec(v_v_444_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_446_, v_i_441_, v___x_447_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_466_, size_t v_i_467_, lean_object* v_bs_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_467_, v_sz_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v_bs_468_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v_bs_x27_472_; lean_object* v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v_bs_x27_472_ = lean_array_uset(v_bs_468_, v_i_467_, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_467_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_472_, v_i_467_, v___x_473_);
v_i_467_ = v___x_475_;
v_bs_468_ = v___x_476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_478_, lean_object* v_i_479_, lean_object* v_bs_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_478_);
lean_dec(v_sz_478_);
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_481_, v_i_boxed_482_, v_bs_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_484_, uint8_t v___x_485_, lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_){
_start:
{
lean_object* v___y_491_; uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_495_ == 0)
{
lean_object* v_fst_496_; uint8_t v___x_497_; 
v_fst_496_ = lean_ctor_get(v_b_489_, 0);
v___x_497_ = lean_unbox(v_fst_496_);
if (v___x_497_ == 0)
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_snd_498_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_507_);
v___x_500_ = v_b_489_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_b_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(v___x_484_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_498_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v___y_491_ = v___x_504_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_snd_508_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_519_);
v___x_510_ = v_b_489_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_dec(v_b_489_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = lean_array_uget_borrowed(v_as_486_, v_i_487_);
lean_inc(v___x_512_);
v___x_513_ = lean_array_push(v_snd_508_, v___x_512_);
v___x_514_ = lean_box(v___x_485_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_513_);
lean_ctor_set(v___x_510_, 0, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_513_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
}
}
}
else
{
return v_b_489_;
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_487_, v___x_492_);
v_i_487_ = v___x_493_;
v_b_489_ = v___y_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_as_522_, lean_object* v_i_523_, lean_object* v_stop_524_, lean_object* v_b_525_){
_start:
{
uint8_t v___x_173647__boxed_526_; uint8_t v___x_173648__boxed_527_; size_t v_i_boxed_528_; size_t v_stop_boxed_529_; lean_object* v_res_530_; 
v___x_173647__boxed_526_ = lean_unbox(v___x_520_);
v___x_173648__boxed_527_ = lean_unbox(v___x_521_);
v_i_boxed_528_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_529_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_173647__boxed_526_, v___x_173648__boxed_527_, v_as_522_, v_i_boxed_528_, v_stop_boxed_529_, v_b_525_);
lean_dec_ref(v_as_522_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_531_, lean_object* v___y_532_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_533_);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_533_);
lean_ctor_set(v___x_534_, 1, v___y_532_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_535_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_535_);
lean_ctor_set(v___x_536_, 1, v___y_532_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_537_, v___y_538_);
lean_dec_ref(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_540_, lean_object* v_stx_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_540_, v_stx_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_a_546_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_555_);
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_584_; 
v_val_556_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_584_ == 0)
{
v___x_558_ = v_a_545_;
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_a_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_snd_560_; 
v_snd_560_ = lean_ctor_get(v_val_556_, 1);
lean_inc(v_snd_560_);
lean_dec(v_val_556_);
if (lean_obj_tag(v_snd_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_558_);
v_a_561_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_544_, 2);
v_a_562_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_snd_560_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_snd_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
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
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_567_, v_a_561_);
lean_dec_ref(v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_583_; 
v_a_571_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_544_, 2);
v_a_572_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_583_ == 0)
{
v___x_574_ = v_snd_560_;
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v_snd_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_a_572_);
v___x_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_582_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_579_, v_a_571_);
lean_dec_ref(v___x_579_);
return v___x_580_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_544_, 0);
v_a_586_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_544_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_544_);
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
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_586_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_594_, lean_object* v_stx_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_594_, v_stx_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_maxRecDepthErrorMessage;
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_607_ = l_Lean_MessageData_ofFormat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_609_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_610_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_ref_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_619_, lean_object* v_declName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_623_ = 0;
v_env_624_ = l_Lean_Environment_setExporting(v_env_619_, v___x_623_);
lean_inc(v_declName_620_);
v___x_625_ = l_Lean_mkPrivateName(v_env_624_, v_declName_620_);
v___x_626_ = 1;
lean_inc_ref(v_env_624_);
v___x_627_ = l_Lean_Environment_contains(v_env_624_, v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_privateToUserName(v_declName_620_);
v___x_629_ = l_Lean_Environment_contains(v_env_624_, v___x_628_, v___x_626_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_622_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declName_620_);
v___x_632_ = lean_box(v___x_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___y_622_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_634_, lean_object* v_declName_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_634_, v_declName_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_toCold_648_; lean_object* v_currRecDepth_649_; lean_object* v_ref_650_; uint16_t v_optionFlags_651_; uint8_t v_suppressElabErrors_652_; uint8_t v_checkDeprecated_653_; uint8_t v_isRecordingDeps_654_; lean_object* v_ref_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_toCold_648_ = lean_ctor_get(v___y_645_, 0);
v_currRecDepth_649_ = lean_ctor_get(v___y_645_, 1);
v_ref_650_ = lean_ctor_get(v___y_645_, 2);
v_optionFlags_651_ = lean_ctor_get_uint16(v___y_645_, sizeof(void*)*3);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 2);
v_checkDeprecated_653_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 3);
v_isRecordingDeps_654_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 4);
v_ref_655_ = l_Lean_replaceRef(v_ref_639_, v_ref_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_toCold_648_);
v___x_656_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_656_, 0, v_toCold_648_);
lean_ctor_set(v___x_656_, 1, v_currRecDepth_649_);
lean_ctor_set(v___x_656_, 2, v_ref_655_);
lean_ctor_set_uint16(v___x_656_, sizeof(void*)*3, v_optionFlags_651_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 2, v_suppressElabErrors_652_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 3, v_checkDeprecated_653_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 4, v_isRecordingDeps_654_);
v___x_657_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___x_656_, v___y_646_);
lean_dec_ref_known(v___x_656_, 3);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_658_, v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_ref_658_);
return v_res_667_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_668_; double v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_float_of_nat(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_ref_680_; lean_object* v___x_681_; lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_727_; 
v_ref_680_ = lean_ctor_get(v___y_677_, 2);
v___x_681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_727_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_727_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_727_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_traceState_687_; lean_object* v_env_688_; lean_object* v_nextMacroScope_689_; lean_object* v_ngen_690_; lean_object* v_auxDeclNGen_691_; lean_object* v_cache_692_; lean_object* v_recordedDeps_693_; lean_object* v_messages_694_; lean_object* v_infoState_695_; lean_object* v_snapshotTasks_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_726_; 
v___x_686_ = lean_st_ref_take(v___y_678_);
v_traceState_687_ = lean_ctor_get(v___x_686_, 4);
v_env_688_ = lean_ctor_get(v___x_686_, 0);
v_nextMacroScope_689_ = lean_ctor_get(v___x_686_, 1);
v_ngen_690_ = lean_ctor_get(v___x_686_, 2);
v_auxDeclNGen_691_ = lean_ctor_get(v___x_686_, 3);
v_cache_692_ = lean_ctor_get(v___x_686_, 5);
v_recordedDeps_693_ = lean_ctor_get(v___x_686_, 6);
v_messages_694_ = lean_ctor_get(v___x_686_, 7);
v_infoState_695_ = lean_ctor_get(v___x_686_, 8);
v_snapshotTasks_696_ = lean_ctor_get(v___x_686_, 9);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_726_ == 0)
{
v___x_698_ = v___x_686_;
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snapshotTasks_696_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_694_);
lean_inc(v_recordedDeps_693_);
lean_inc(v_cache_692_);
lean_inc(v_traceState_687_);
lean_inc(v_auxDeclNGen_691_);
lean_inc(v_ngen_690_);
lean_inc(v_nextMacroScope_689_);
lean_inc(v_env_688_);
lean_dec(v___x_686_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint64_t v_tid_700_; lean_object* v_traces_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_725_; 
v_tid_700_ = lean_ctor_get_uint64(v_traceState_687_, sizeof(void*)*1);
v_traces_701_ = lean_ctor_get(v_traceState_687_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_traceState_687_);
if (v_isSharedCheck_725_ == 0)
{
v___x_703_ = v_traceState_687_;
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_traces_701_);
lean_dec(v_traceState_687_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; double v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_705_ = lean_box(0);
v___x_706_ = lean_box(0);
v___x_707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_708_ = 0;
v___x_709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_710_, 0, v_cls_673_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3, v___x_707_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3 + 8, v___x_707_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*3 + 16, v___x_708_);
v___x_711_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_712_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v_a_682_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_inc(v_ref_680_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_680_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_traces_701_, v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_714_);
lean_ctor_set_uint64(v_reuseFailAlloc_724_, sizeof(void*)*1, v_tid_700_);
v___x_716_ = v_reuseFailAlloc_724_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 4, v___x_716_);
v___x_718_ = v___x_698_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_env_688_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_nextMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_ngen_690_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_auxDeclNGen_691_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_723_, 5, v_cache_692_);
lean_ctor_set(v_reuseFailAlloc_723_, 6, v_recordedDeps_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 7, v_messages_694_);
lean_ctor_set(v_reuseFailAlloc_723_, 8, v_infoState_695_);
lean_ctor_set(v_reuseFailAlloc_723_, 9, v_snapshotTasks_696_);
v___x_718_ = v_reuseFailAlloc_723_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_put(v___y_678_, v___x_718_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_705_);
v___x_721_ = v___x_684_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_705_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_728_, v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
if (lean_obj_tag(v_as_739_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_toCold_749_; lean_object* v_options_750_; uint8_t v_hasTrace_751_; 
v_toCold_749_ = lean_ctor_get(v___y_744_, 0);
v_options_750_ = lean_ctor_get(v_toCold_749_, 2);
v_hasTrace_751_ = lean_ctor_get_uint8(v_options_750_, sizeof(void*)*1);
if (v_hasTrace_751_ == 0)
{
lean_object* v_tail_752_; 
v_tail_752_ = lean_ctor_get(v_as_739_, 1);
lean_inc(v_tail_752_);
lean_dec_ref_known(v_as_739_, 2);
v_as_739_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v_inheritedTraceOptions_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_head_754_ = lean_ctor_get(v_as_739_, 0);
lean_inc(v_head_754_);
v_tail_755_ = lean_ctor_get(v_as_739_, 1);
lean_inc(v_tail_755_);
lean_dec_ref_known(v_as_739_, 2);
v_fst_756_ = lean_ctor_get(v_head_754_, 0);
lean_inc_n(v_fst_756_, 2);
v_snd_757_ = lean_ctor_get(v_head_754_, 1);
lean_inc(v_snd_757_);
lean_dec(v_head_754_);
v_inheritedTraceOptions_758_ = lean_ctor_get(v_toCold_749_, 11);
v___x_759_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_760_ = l_Lean_Name_append(v___x_759_, v_fst_756_);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_758_, v_options_750_, v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v_snd_757_);
lean_dec(v_fst_756_);
v_as_739_ = v_tail_755_;
goto _start;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_763_, 0, v_snd_757_);
v___x_764_ = l_Lean_MessageData_ofFormat(v___x_763_);
v___x_765_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_756_, v___x_764_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
v_as_739_ = v_tail_755_;
goto _start;
}
else
{
lean_dec(v_tail_755_);
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg(lean_object* v_a_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v_key_779_; lean_object* v_value_780_; lean_object* v_tail_781_; uint8_t v___x_782_; 
v_key_779_ = lean_ctor_get(v_x_777_, 0);
v_value_780_ = lean_ctor_get(v_x_777_, 1);
v_tail_781_ = lean_ctor_get(v_x_777_, 2);
v___x_782_ = lean_name_eq(v_key_779_, v_a_776_);
if (v___x_782_ == 0)
{
v_x_777_ = v_tail_781_;
goto _start;
}
else
{
lean_object* v___x_784_; 
lean_inc(v_value_780_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_value_780_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg___boxed(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg(v_a_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec(v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_buckets_790_; lean_object* v___x_791_; uint64_t v___y_793_; 
v_buckets_790_ = lean_ctor_get(v_m_788_, 1);
v___x_791_ = lean_array_get_size(v_buckets_790_);
if (lean_obj_tag(v_a_789_) == 0)
{
uint64_t v___x_807_; 
v___x_807_ = 1723ULL;
v___y_793_ = v___x_807_;
goto v___jp_792_;
}
else
{
uint64_t v_hash_808_; 
v_hash_808_ = lean_ctor_get_uint64(v_a_789_, sizeof(void*)*2);
v___y_793_ = v_hash_808_;
goto v___jp_792_;
}
v___jp_792_:
{
uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v_fold_796_; uint64_t v___x_797_; uint64_t v___x_798_; uint64_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_794_ = 32ULL;
v___x_795_ = lean_uint64_shift_right(v___y_793_, v___x_794_);
v_fold_796_ = lean_uint64_xor(v___y_793_, v___x_795_);
v___x_797_ = 16ULL;
v___x_798_ = lean_uint64_shift_right(v_fold_796_, v___x_797_);
v___x_799_ = lean_uint64_xor(v_fold_796_, v___x_798_);
v___x_800_ = lean_uint64_to_usize(v___x_799_);
v___x_801_ = lean_usize_of_nat(v___x_791_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_sub(v___x_801_, v___x_802_);
v___x_804_ = lean_usize_land(v___x_800_, v___x_803_);
v___x_805_ = lean_array_uget_borrowed(v_buckets_790_, v___x_804_);
v___x_806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg(v_a_789_, v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_m_809_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_812_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg(){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__1);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___boxed(lean_object* v___dummy_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg();
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object* v___x_819_, lean_object* v_entry_820_, lean_object* v_s_821_){
_start:
{
lean_object* v_addEntryFn_822_; lean_object* v_importedEntries_823_; lean_object* v_state_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
v_addEntryFn_822_ = lean_ctor_get(v___x_819_, 3);
lean_inc(v_addEntryFn_822_);
lean_dec_ref(v___x_819_);
v_importedEntries_823_ = lean_ctor_get(v_s_821_, 0);
v_state_824_ = lean_ctor_get(v_s_821_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_s_821_);
if (v_isSharedCheck_832_ == 0)
{
v___x_826_ = v_s_821_;
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_state_824_);
lean_inc(v_importedEntries_823_);
lean_dec(v_s_821_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_state_828_; lean_object* v___x_830_; 
v_state_828_ = lean_apply_2(v_addEntryFn_822_, v_state_824_, v_entry_820_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_state_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_importedEntries_823_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_state_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_833_, lean_object* v_i_834_, lean_object* v_k_835_){
_start:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_get_size(v_keys_833_);
v___x_837_ = lean_nat_dec_lt(v_i_834_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec(v_i_834_);
return v___x_837_;
}
else
{
lean_object* v_k_x27_838_; uint8_t v___x_839_; 
v_k_x27_838_ = lean_array_fget_borrowed(v_keys_833_, v_i_834_);
v___x_839_ = l_Lean_instBEqExtraModUse_beq(v_k_835_, v_k_x27_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_i_834_, v___x_840_);
lean_dec(v_i_834_);
v_i_834_ = v___x_841_;
goto _start;
}
else
{
lean_dec(v_i_834_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_843_, lean_object* v_i_844_, lean_object* v_k_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_843_, v_i_844_, v_k_845_);
lean_dec_ref(v_k_845_);
lean_dec_ref(v_keys_843_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_848_, size_t v_x_849_, lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_es_851_; lean_object* v___x_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v_j_855_; lean_object* v___x_856_; 
v_es_851_ = lean_ctor_get(v_x_848_, 0);
v___x_852_ = lean_box(2);
v___x_853_ = ((size_t)31ULL);
v___x_854_ = lean_usize_land(v_x_849_, v___x_853_);
v_j_855_ = lean_usize_to_nat(v___x_854_);
v___x_856_ = lean_array_get_borrowed(v___x_852_, v_es_851_, v_j_855_);
lean_dec(v_j_855_);
switch(lean_obj_tag(v___x_856_))
{
case 0:
{
lean_object* v_key_857_; uint8_t v___x_858_; 
v_key_857_ = lean_ctor_get(v___x_856_, 0);
v___x_858_ = l_Lean_instBEqExtraModUse_beq(v_x_850_, v_key_857_);
return v___x_858_;
}
case 1:
{
lean_object* v_node_859_; size_t v___x_860_; size_t v___x_861_; 
v_node_859_ = lean_ctor_get(v___x_856_, 0);
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_usize_shift_right(v_x_849_, v___x_860_);
v_x_848_ = v_node_859_;
v_x_849_ = v___x_861_;
goto _start;
}
default: 
{
uint8_t v___x_863_; 
v___x_863_ = 0;
return v___x_863_;
}
}
}
else
{
lean_object* v_ks_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_ks_864_ = lean_ctor_get(v_x_848_, 0);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_864_, v___x_865_, v_x_850_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
size_t v_x_174186__boxed_870_; uint8_t v_res_871_; lean_object* v_r_872_; 
v_x_174186__boxed_870_ = lean_unbox_usize(v_x_868_);
lean_dec(v_x_868_);
v_res_871_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_867_, v_x_174186__boxed_870_, v_x_869_);
lean_dec_ref(v_x_869_);
lean_dec_ref(v_x_867_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
uint64_t v___x_875_; size_t v___x_876_; uint8_t v___x_877_; 
v___x_875_ = l_Lean_instHashableExtraModUse_hash(v_x_874_);
v___x_876_ = lean_uint64_to_usize(v___x_875_);
v___x_877_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_873_, v___x_876_, v_x_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_878_, v_x_879_);
lean_dec_ref(v_x_879_);
lean_dec_ref(v_x_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg___closed__0);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34___redArg();
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
lean_ctor_set(v___x_891_, 2, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_892_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_893_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_894_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_895_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_896_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
lean_ctor_set(v___x_896_, 2, v___x_893_);
lean_ctor_set(v___x_896_, 3, v___x_894_);
lean_ctor_set(v___x_896_, 4, v___x_894_);
lean_ctor_set(v___x_896_, 5, v___x_894_);
lean_ctor_set(v___x_896_, 6, v___x_894_);
lean_ctor_set(v___x_896_, 7, v___x_892_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_cls_909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_910_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_911_ = l_Lean_Name_append(v___x_910_, v_cls_909_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_922_, uint8_t v_isMeta_923_, lean_object* v_hint_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_env_966_; uint8_t v_isExporting_967_; lean_object* v_entry_968_; lean_object* v___x_969_; lean_object* v_env_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_964_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
v___x_965_ = lean_st_ref_get(v___y_930_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_966_);
lean_dec(v___x_965_);
v_isExporting_967_ = lean_ctor_get_uint8(v_env_966_, sizeof(void*)*13);
lean_dec_ref(v_env_966_);
lean_inc(v_mod_922_);
v_entry_968_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_968_, 0, v_mod_922_);
lean_ctor_set_uint8(v_entry_968_, sizeof(void*)*1, v_isExporting_967_);
lean_ctor_set_uint8(v_entry_968_, sizeof(void*)*1 + 1, v_isMeta_923_);
v___x_969_ = lean_st_ref_get(v___y_930_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_972_ = lean_box(1);
v___x_973_ = lean_box(0);
v___x_974_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_964_, v___x_971_, v_env_970_, v___x_972_, v___x_973_);
v___x_975_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_974_, v_entry_968_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v_toCold_976_; lean_object* v_options_977_; lean_object* v_inheritedTraceOptions_978_; uint8_t v_hasTrace_979_; lean_object* v___f_980_; uint8_t v___x_981_; lean_object* v___y_983_; lean_object* v___y_984_; 
v_toCold_976_ = lean_ctor_get(v___y_929_, 0);
v_options_977_ = lean_ctor_get(v_toCold_976_, 2);
v_inheritedTraceOptions_978_ = lean_ctor_get(v_toCold_976_, 11);
v_hasTrace_979_ = lean_ctor_get_uint8(v_options_977_, sizeof(void*)*1);
v___f_980_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0), 3, 2);
lean_closure_set(v___f_980_, 0, v___x_971_);
lean_closure_set(v___f_980_, 1, v_entry_968_);
v___x_981_ = 1;
if (v_hasTrace_979_ == 0)
{
lean_dec(v_hint_924_);
lean_dec(v_mod_922_);
v___y_983_ = v___y_928_;
v___y_984_ = v___y_930_;
goto v___jp_982_;
}
else
{
lean_object* v_cls_1011_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_cls_1011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_1031_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_1032_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_978_, v_options_977_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec(v_hint_924_);
lean_dec(v_mod_922_);
v___y_983_ = v___y_928_;
v___y_984_ = v___y_930_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1033_; lean_object* v___y_1035_; 
v___x_1033_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_967_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_1035_ = v___x_1042_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_1035_ = v___x_1043_;
goto v___jp_1034_;
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_inc_ref(v___y_1035_);
v___x_1036_ = l_Lean_stringToMessageData(v___y_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1033_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
if (v_isMeta_923_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_1018_ = v___x_1039_;
v___y_1019_ = v___x_1040_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_1018_ = v___x_1039_;
v___y_1019_ = v___x_1041_;
goto v___jp_1017_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___y_1013_);
lean_ctor_set(v___x_1015_, 1, v___y_1014_);
v___x_1016_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_1011_, v___x_1015_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref_known(v___x_1016_, 1);
v___y_983_ = v___y_928_;
v___y_984_ = v___y_930_;
goto v___jp_982_;
}
else
{
lean_dec_ref(v___f_980_);
return v___x_1016_;
}
}
v___jp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
lean_inc_ref(v___y_1019_);
v___x_1020_ = l_Lean_stringToMessageData(v___y_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___y_1018_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_MessageData_ofName(v_mod_922_);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Lean_Name_isAnonymous(v_hint_924_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_1028_ = l_Lean_MessageData_ofName(v_hint_924_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___y_1013_ = v___x_1025_;
v___y_1014_ = v___x_1029_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_hint_924_);
v___x_1030_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_1013_ = v___x_1025_;
v___y_1014_ = v___x_1030_;
goto v___jp_1012_;
}
}
}
v___jp_982_:
{
lean_object* v___x_985_; lean_object* v_toEnvExtension_986_; uint8_t v_logWrites_987_; 
v___x_985_ = lean_st_ref_take(v___y_984_);
v_toEnvExtension_986_ = lean_ctor_get(v___x_971_, 0);
v_logWrites_987_ = lean_ctor_get_uint8(v_toEnvExtension_986_, sizeof(void*)*6);
if (v_logWrites_987_ == 0)
{
lean_object* v_env_988_; lean_object* v_nextMacroScope_989_; lean_object* v_ngen_990_; lean_object* v_auxDeclNGen_991_; lean_object* v_traceState_992_; lean_object* v_recordedDeps_993_; lean_object* v_messages_994_; lean_object* v_infoState_995_; lean_object* v_snapshotTasks_996_; lean_object* v_asyncMode_997_; lean_object* v___x_998_; 
v_env_988_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_988_);
v_nextMacroScope_989_ = lean_ctor_get(v___x_985_, 1);
lean_inc(v_nextMacroScope_989_);
v_ngen_990_ = lean_ctor_get(v___x_985_, 2);
lean_inc_ref(v_ngen_990_);
v_auxDeclNGen_991_ = lean_ctor_get(v___x_985_, 3);
lean_inc_ref(v_auxDeclNGen_991_);
v_traceState_992_ = lean_ctor_get(v___x_985_, 4);
lean_inc_ref(v_traceState_992_);
v_recordedDeps_993_ = lean_ctor_get(v___x_985_, 6);
lean_inc_ref(v_recordedDeps_993_);
v_messages_994_ = lean_ctor_get(v___x_985_, 7);
lean_inc_ref(v_messages_994_);
v_infoState_995_ = lean_ctor_get(v___x_985_, 8);
lean_inc_ref(v_infoState_995_);
v_snapshotTasks_996_ = lean_ctor_get(v___x_985_, 9);
lean_inc_ref(v_snapshotTasks_996_);
lean_dec(v___x_985_);
v_asyncMode_997_ = lean_ctor_get(v_toEnvExtension_986_, 2);
lean_inc_ref(v_toEnvExtension_986_);
v___x_998_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_986_, v_env_988_, v___f_980_, v_asyncMode_997_, v___x_973_, v___x_981_);
v___y_933_ = v_messages_994_;
v___y_934_ = v___y_983_;
v___y_935_ = v_recordedDeps_993_;
v___y_936_ = v_auxDeclNGen_991_;
v___y_937_ = v___y_984_;
v___y_938_ = v_snapshotTasks_996_;
v___y_939_ = v_ngen_990_;
v___y_940_ = v_infoState_995_;
v___y_941_ = v_nextMacroScope_989_;
v___y_942_ = v_traceState_992_;
v___y_943_ = v___x_998_;
goto v___jp_932_;
}
else
{
lean_object* v_env_999_; lean_object* v_nextMacroScope_1000_; lean_object* v_ngen_1001_; lean_object* v_auxDeclNGen_1002_; lean_object* v_traceState_1003_; lean_object* v_recordedDeps_1004_; lean_object* v_messages_1005_; lean_object* v_infoState_1006_; lean_object* v_snapshotTasks_1007_; lean_object* v_asyncMode_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_env_999_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_999_);
v_nextMacroScope_1000_ = lean_ctor_get(v___x_985_, 1);
lean_inc(v_nextMacroScope_1000_);
v_ngen_1001_ = lean_ctor_get(v___x_985_, 2);
lean_inc_ref(v_ngen_1001_);
v_auxDeclNGen_1002_ = lean_ctor_get(v___x_985_, 3);
lean_inc_ref(v_auxDeclNGen_1002_);
v_traceState_1003_ = lean_ctor_get(v___x_985_, 4);
lean_inc_ref(v_traceState_1003_);
v_recordedDeps_1004_ = lean_ctor_get(v___x_985_, 6);
lean_inc_ref(v_recordedDeps_1004_);
v_messages_1005_ = lean_ctor_get(v___x_985_, 7);
lean_inc_ref(v_messages_1005_);
v_infoState_1006_ = lean_ctor_get(v___x_985_, 8);
lean_inc_ref(v_infoState_1006_);
v_snapshotTasks_1007_ = lean_ctor_get(v___x_985_, 9);
lean_inc_ref(v_snapshotTasks_1007_);
lean_dec(v___x_985_);
v_asyncMode_1008_ = lean_ctor_get(v_toEnvExtension_986_, 2);
lean_inc_ref_n(v_toEnvExtension_986_, 2);
v___x_1009_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_986_, v_env_999_);
lean_dec_ref(v_env_999_);
v___x_1010_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_986_, v___x_1009_, v___f_980_, v_asyncMode_1008_, v___x_973_, v___x_981_);
v___y_933_ = v_messages_1005_;
v___y_934_ = v___y_983_;
v___y_935_ = v_recordedDeps_1004_;
v___y_936_ = v_auxDeclNGen_1002_;
v___y_937_ = v___y_984_;
v___y_938_ = v_snapshotTasks_1007_;
v___y_939_ = v_ngen_1001_;
v___y_940_ = v_infoState_1006_;
v___y_941_ = v_nextMacroScope_1000_;
v___y_942_ = v_traceState_1003_;
v___y_943_ = v___x_1010_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref_known(v_entry_968_, 1);
lean_dec(v_hint_924_);
lean_dec(v_mod_922_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
v___jp_932_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_mctx_948_; lean_object* v_zetaDeltaFVarIds_949_; lean_object* v_postponed_950_; lean_object* v_diag_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_962_; 
v___x_944_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_945_, 0, v___y_943_);
lean_ctor_set(v___x_945_, 1, v___y_941_);
lean_ctor_set(v___x_945_, 2, v___y_939_);
lean_ctor_set(v___x_945_, 3, v___y_936_);
lean_ctor_set(v___x_945_, 4, v___y_942_);
lean_ctor_set(v___x_945_, 5, v___x_944_);
lean_ctor_set(v___x_945_, 6, v___y_935_);
lean_ctor_set(v___x_945_, 7, v___y_933_);
lean_ctor_set(v___x_945_, 8, v___y_940_);
lean_ctor_set(v___x_945_, 9, v___y_938_);
v___x_946_ = lean_st_ref_put(v___y_937_, v___x_945_);
v___x_947_ = lean_st_ref_take(v___y_934_);
v_mctx_948_ = lean_ctor_get(v___x_947_, 0);
v_zetaDeltaFVarIds_949_ = lean_ctor_get(v___x_947_, 2);
v_postponed_950_ = lean_ctor_get(v___x_947_, 3);
v_diag_951_ = lean_ctor_get(v___x_947_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v___x_947_, 1);
lean_dec(v_unused_963_);
v___x_953_ = v___x_947_;
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_diag_951_);
lean_inc(v_postponed_950_);
lean_inc(v_zetaDeltaFVarIds_949_);
lean_inc(v_mctx_948_);
lean_dec(v___x_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_962_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_955_ = lean_box(0);
v___x_956_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_mctx_948_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_zetaDeltaFVarIds_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_postponed_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_diag_951_);
v___x_958_ = v_reuseFailAlloc_961_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_st_ref_put(v___y_934_, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_955_);
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1046_, lean_object* v_isMeta_1047_, lean_object* v_hint_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_isMeta_boxed_1056_; lean_object* v_res_1057_; 
v_isMeta_boxed_1056_ = lean_unbox(v_isMeta_1047_);
v_res_1057_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1046_, v_isMeta_boxed_1056_, v_hint_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1058_, lean_object* v_declName_1059_, lean_object* v_as_1060_, size_t v_sz_1061_, size_t v_i_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1062_, v_sz_1061_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_declName_1059_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_b_1063_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v_modules_1074_; lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v_toImport_1078_; lean_object* v_module_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1073_ = l_Lean_Environment_header(v___x_1058_);
v_modules_1074_ = lean_ctor_get(v___x_1073_, 3);
lean_inc_ref(v_modules_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1076_ = lean_array_uget_borrowed(v_as_1060_, v_i_1062_);
v___x_1077_ = lean_array_get(v___x_1075_, v_modules_1074_, v_a_1076_);
lean_dec_ref(v_modules_1074_);
v_toImport_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_toImport_1078_);
lean_dec(v___x_1077_);
v_module_1079_ = lean_ctor_get(v_toImport_1078_, 0);
lean_inc(v_module_1079_);
lean_dec_ref(v_toImport_1078_);
v___x_1080_ = lean_box(0);
v___x_1081_ = 0;
lean_inc(v_declName_1059_);
v___x_1082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1079_, v___x_1081_, v_declName_1059_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1082_) == 0)
{
size_t v___x_1083_; size_t v___x_1084_; 
lean_dec_ref_known(v___x_1082_, 1);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1062_, v___x_1083_);
v_i_1062_ = v___x_1084_;
v_b_1063_ = v___x_1080_;
goto _start;
}
else
{
lean_dec(v_declName_1059_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1086_, lean_object* v_declName_1087_, lean_object* v_as_1088_, lean_object* v_sz_1089_, lean_object* v_i_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
size_t v_sz_boxed_1099_; size_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_sz_boxed_1099_ = lean_unbox_usize(v_sz_1089_);
lean_dec(v_sz_1089_);
v_i_boxed_1100_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1086_, v_declName_1087_, v_as_1088_, v_sz_boxed_1099_, v_i_boxed_1100_, v_b_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v_as_1088_);
lean_dec_ref(v___x_1086_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1105_, uint8_t v_isMeta_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_env_1119_; lean_object* v___y_1121_; lean_object* v___x_1134_; 
v___x_1114_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1115_ = lean_st_ref_get(v___y_1112_);
v_env_1119_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1119_);
lean_dec(v___x_1115_);
v___x_1134_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1119_, v_declName_1105_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1105_);
goto v___jp_1116_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1136_; lean_object* v_modules_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_val_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Environment_header(v_env_1119_);
v_modules_1137_ = lean_ctor_get(v___x_1136_, 3);
lean_inc_ref(v_modules_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_array_get_size(v_modules_1137_);
v___x_1139_ = lean_nat_dec_lt(v_val_1135_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_dec_ref(v_modules_1137_);
lean_dec(v_val_1135_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1105_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___y_1143_; 
v___x_1140_ = lean_array_fget(v_modules_1137_, v_val_1135_);
lean_dec(v_val_1135_);
lean_dec_ref(v_modules_1137_);
v___x_1141_ = lean_st_ref_get(v___y_1112_);
if (v_isMeta_1106_ == 0)
{
lean_dec(v___x_1141_);
v___y_1143_ = v_isMeta_1106_;
goto v___jp_1142_;
}
else
{
lean_object* v_env_1154_; uint8_t v___x_1155_; 
v_env_1154_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_env_1154_);
lean_dec(v___x_1141_);
lean_inc(v_declName_1105_);
v___x_1155_ = l_Lean_isMarkedMeta(v_env_1154_, v_declName_1105_);
if (v___x_1155_ == 0)
{
v___y_1143_ = v_isMeta_1106_;
goto v___jp_1142_;
}
else
{
uint8_t v___x_1156_; 
v___x_1156_ = 0;
v___y_1143_ = v___x_1156_;
goto v___jp_1142_;
}
}
v___jp_1142_:
{
lean_object* v_toImport_1144_; lean_object* v_module_1145_; lean_object* v___x_1146_; 
v_toImport_1144_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_toImport_1144_);
lean_dec(v___x_1140_);
v_module_1145_ = lean_ctor_get(v_toImport_1144_, 0);
lean_inc(v_module_1145_);
lean_dec_ref(v_toImport_1144_);
lean_inc(v_declName_1105_);
v___x_1146_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1145_, v___y_1143_, v_declName_1105_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1146_, 1);
v___x_1147_ = l_Lean_indirectModUseExt;
v___x_1148_ = lean_box(1);
v___x_1149_ = lean_box(0);
lean_inc_ref(v_env_1119_);
v___x_1150_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1114_, v___x_1147_, v_env_1119_, v___x_1148_, v___x_1149_);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1150_, v_declName_1105_);
lean_dec(v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1121_ = v___x_1152_;
goto v___jp_1120_;
}
else
{
lean_object* v_val_1153_; 
v_val_1153_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1151_, 1);
v___y_1121_ = v_val_1153_;
goto v___jp_1120_;
}
}
else
{
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1105_);
return v___x_1146_;
}
}
}
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
v___jp_1120_:
{
lean_object* v___x_1122_; size_t v_sz_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_box(0);
v_sz_1123_ = lean_array_size(v___y_1121_);
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1119_, v_declName_1105_, v___y_1121_, v_sz_1123_, v___x_1124_, v___x_1122_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_env_1119_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1133_);
v___x_1127_ = v___x_1125_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v___x_1125_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1122_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1122_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1157_, lean_object* v_isMeta_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_isMeta_boxed_1166_; lean_object* v_res_1167_; 
v_isMeta_boxed_1166_ = lean_unbox(v_isMeta_1158_);
v_res_1167_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1157_, v_isMeta_boxed_1166_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
if (lean_obj_tag(v_as_x27_1168_) == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1169_);
return v___x_1177_;
}
else
{
lean_object* v_head_1178_; lean_object* v_tail_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; 
v_head_1178_ = lean_ctor_get(v_as_x27_1168_, 0);
v_tail_1179_ = lean_ctor_get(v_as_x27_1168_, 1);
v___x_1180_ = lean_box(0);
v___x_1181_ = 1;
lean_inc(v_head_1178_);
v___x_1182_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1178_, v___x_1181_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_dec_ref_known(v___x_1182_, 1);
v_as_x27_1168_ = v_tail_1179_;
v_b_1169_ = v___x_1180_;
goto _start;
}
else
{
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1184_, lean_object* v_b_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1184_, v_b_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_as_x27_1184_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_currNamespace_1194_);
lean_ctor_set(v___x_1197_, 1, v___y_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1198_, v___y_1199_, v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1202_, lean_object* v___x_1203_, lean_object* v_currNamespace_1204_, lean_object* v_openDecls_1205_, lean_object* v_n_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = l_Lean_ResolveName_resolveGlobalName(v_env_1202_, v___x_1203_, v_currNamespace_1204_, v_openDecls_1205_, v_n_1206_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1211_, lean_object* v___x_1212_, lean_object* v_currNamespace_1213_, lean_object* v_openDecls_1214_, lean_object* v_n_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1211_, v___x_1212_, v_currNamespace_1213_, v_openDecls_1214_, v_n_1215_, v___y_1216_, v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___x_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1219_, lean_object* v_currNamespace_1220_, lean_object* v_openDecls_1221_, lean_object* v_n_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = l_Lean_ResolveName_resolveNamespace(v_env_1219_, v_currNamespace_1220_, v_openDecls_1221_, v_n_1222_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1227_, lean_object* v_currNamespace_1228_, lean_object* v_openDecls_1229_, lean_object* v_n_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1227_, v_currNamespace_1228_, v_openDecls_1229_, v_n_1230_, v___y_1231_, v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_toCold_1244_; lean_object* v_env_1245_; lean_object* v_currRecDepth_1246_; lean_object* v_ref_1247_; lean_object* v_maxRecDepth_1248_; lean_object* v_currNamespace_1249_; lean_object* v_openDecls_1250_; lean_object* v_quotContext_1251_; lean_object* v_currMacroScope_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v_methods_1259_; lean_object* v___x_1260_; lean_object* v_nextMacroScope_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1243_ = lean_st_ref_get(v___y_1241_);
v_toCold_1244_ = lean_ctor_get(v___y_1240_, 0);
v_env_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref_n(v_env_1245_, 4);
lean_dec(v___x_1243_);
v_currRecDepth_1246_ = lean_ctor_get(v___y_1240_, 1);
v_ref_1247_ = lean_ctor_get(v___y_1240_, 2);
v_maxRecDepth_1248_ = lean_ctor_get(v_toCold_1244_, 3);
v_currNamespace_1249_ = lean_ctor_get(v_toCold_1244_, 4);
v_openDecls_1250_ = lean_ctor_get(v_toCold_1244_, 5);
v_quotContext_1251_ = lean_ctor_get(v_toCold_1244_, 8);
v_currMacroScope_1252_ = lean_ctor_get(v_toCold_1244_, 9);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1253_, 0, v_env_1245_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1254_, 0, v_env_1245_);
v___x_1255_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1240_);
lean_inc_n(v_currNamespace_1249_, 3);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1256_, 0, v_currNamespace_1249_);
lean_inc_n(v_openDecls_1250_, 2);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1257_, 0, v_env_1245_);
lean_closure_set(v___f_1257_, 1, v___x_1255_);
lean_closure_set(v___f_1257_, 2, v_currNamespace_1249_);
lean_closure_set(v___f_1257_, 3, v_openDecls_1250_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1258_, 0, v_env_1245_);
lean_closure_set(v___f_1258_, 1, v_currNamespace_1249_);
lean_closure_set(v___f_1258_, 2, v_openDecls_1250_);
v_methods_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1259_, 0, v___f_1254_);
lean_ctor_set(v_methods_1259_, 1, v___f_1256_);
lean_ctor_set(v_methods_1259_, 2, v___f_1253_);
lean_ctor_set(v_methods_1259_, 3, v___f_1258_);
lean_ctor_set(v_methods_1259_, 4, v___f_1257_);
v___x_1260_ = lean_st_ref_get(v___y_1241_);
v_nextMacroScope_1261_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_nextMacroScope_1261_);
lean_dec(v___x_1260_);
lean_inc(v_ref_1247_);
lean_inc(v_maxRecDepth_1248_);
lean_inc(v_currRecDepth_1246_);
lean_inc(v_currMacroScope_1252_);
lean_inc(v_quotContext_1251_);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v_methods_1259_);
lean_ctor_set(v___x_1262_, 1, v_quotContext_1251_);
lean_ctor_set(v___x_1262_, 2, v_currMacroScope_1252_);
lean_ctor_set(v___x_1262_, 3, v_currRecDepth_1246_);
lean_ctor_set(v___x_1262_, 4, v_maxRecDepth_1248_);
lean_ctor_set(v___x_1262_, 5, v_ref_1247_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1264_, 0, v_nextMacroScope_1261_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
v___x_1265_ = lean_apply_2(v_x_1235_, v___x_1262_, v___x_1264_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v_macroScope_1268_; lean_object* v_traceMsgs_1269_; lean_object* v_expandedMacroDecls_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_a_1266_);
v_a_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1265_, 2);
v_macroScope_1268_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_macroScope_1268_);
v_traceMsgs_1269_ = lean_ctor_get(v_a_1266_, 1);
lean_inc(v_traceMsgs_1269_);
v_expandedMacroDecls_1270_ = lean_ctor_get(v_a_1266_, 2);
lean_inc(v_expandedMacroDecls_1270_);
lean_dec(v_a_1266_);
v___x_1271_ = lean_box(0);
v___x_1272_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1270_, v___x_1271_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v_expandedMacroDecls_1270_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v_env_1274_; lean_object* v_ngen_1275_; lean_object* v_auxDeclNGen_1276_; lean_object* v_traceState_1277_; lean_object* v_cache_1278_; lean_object* v_recordedDeps_1279_; lean_object* v_messages_1280_; lean_object* v_infoState_1281_; lean_object* v_snapshotTasks_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref_known(v___x_1272_, 1);
v___x_1273_ = lean_st_ref_take(v___y_1241_);
v_env_1274_ = lean_ctor_get(v___x_1273_, 0);
v_ngen_1275_ = lean_ctor_get(v___x_1273_, 2);
v_auxDeclNGen_1276_ = lean_ctor_get(v___x_1273_, 3);
v_traceState_1277_ = lean_ctor_get(v___x_1273_, 4);
v_cache_1278_ = lean_ctor_get(v___x_1273_, 5);
v_recordedDeps_1279_ = lean_ctor_get(v___x_1273_, 6);
v_messages_1280_ = lean_ctor_get(v___x_1273_, 7);
v_infoState_1281_ = lean_ctor_get(v___x_1273_, 8);
v_snapshotTasks_1282_ = lean_ctor_get(v___x_1273_, 9);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1273_, 1);
lean_dec(v_unused_1309_);
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1308_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_snapshotTasks_1282_);
lean_inc(v_infoState_1281_);
lean_inc(v_messages_1280_);
lean_inc(v_recordedDeps_1279_);
lean_inc(v_cache_1278_);
lean_inc(v_traceState_1277_);
lean_inc(v_auxDeclNGen_1276_);
lean_inc(v_ngen_1275_);
lean_inc(v_env_1274_);
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1308_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_macroScope_1268_);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_env_1274_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_macroScope_1268_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_ngen_1275_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_auxDeclNGen_1276_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v_traceState_1277_);
lean_ctor_set(v_reuseFailAlloc_1307_, 5, v_cache_1278_);
lean_ctor_set(v_reuseFailAlloc_1307_, 6, v_recordedDeps_1279_);
lean_ctor_set(v_reuseFailAlloc_1307_, 7, v_messages_1280_);
lean_ctor_set(v_reuseFailAlloc_1307_, 8, v_infoState_1281_);
lean_ctor_set(v_reuseFailAlloc_1307_, 9, v_snapshotTasks_1282_);
v___x_1287_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_st_ref_put(v___y_1241_, v___x_1287_);
v___x_1289_ = l_List_reverse___redArg(v_traceMsgs_1269_);
v___x_1290_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1289_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___x_1290_, 0);
lean_dec(v_unused_1298_);
v___x_1292_ = v___x_1290_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v___x_1290_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v_a_1267_);
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1267_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_a_1267_);
v_a_1299_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1290_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1290_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_traceMsgs_1269_);
lean_dec(v_macroScope_1268_);
lean_dec(v_a_1267_);
v_a_1310_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1272_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1272_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1265_, 2);
if (lean_obj_tag(v_a_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_a_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_a_1319_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_a_1319_);
v_a_1320_ = lean_ctor_get(v_a_1318_, 1);
lean_inc_ref(v_a_1320_);
lean_dec_ref_known(v_a_1318_, 2);
v___x_1321_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1322_ = lean_string_dec_eq(v_a_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_a_1320_);
v___x_1324_ = l_Lean_MessageData_ofFormat(v___x_1323_);
v___x_1325_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1319_, v___x_1324_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v_a_1319_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; 
lean_dec_ref(v_a_1320_);
v___x_1326_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1319_);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_bs_1342_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_bs_1342_);
return v___x_1344_;
}
else
{
lean_object* v_v_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_v_1345_ = lean_array_uget(v_bs_1342_, v_i_1341_);
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1345_);
v___x_1347_ = l_Lean_Syntax_isOfKind(v_v_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_v_1345_);
lean_dec_ref(v_bs_1342_);
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = l_Lean_Syntax_getArg(v_v_1345_, v___x_1349_);
v___x_1351_ = l_Lean_Syntax_isOfKind(v___x_1350_, v___x_1346_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_v_1345_);
lean_dec_ref(v_bs_1342_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v_bs_x27_1354_; lean_object* v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = lean_unsigned_to_nat(3u);
v_bs_x27_1354_ = lean_array_uset(v_bs_1342_, v_i_1341_, v___x_1349_);
v___x_1355_ = l_Lean_Syntax_getArg(v_v_1345_, v___x_1353_);
lean_dec(v_v_1345_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1341_, v___x_1356_);
v___x_1358_ = lean_array_uset(v_bs_x27_1354_, v_i_1341_, v___x_1355_);
v_i_1341_ = v___x_1357_;
v_bs_1342_ = v___x_1358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1360_, lean_object* v_i_1361_, lean_object* v_bs_1362_){
_start:
{
size_t v_sz_boxed_1363_; size_t v_i_boxed_1364_; lean_object* v_res_1365_; 
v_sz_boxed_1363_ = lean_unbox_usize(v_sz_1360_);
lean_dec(v_sz_1360_);
v_i_boxed_1364_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1363_, v_i_boxed_1364_, v_bs_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_bs_1380_){
_start:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_usize_dec_lt(v_i_1379_, v_sz_1378_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v_bs_1380_);
return v___x_1382_;
}
else
{
lean_object* v_v_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_v_1383_ = lean_array_uget(v_bs_1380_, v_i_1379_);
v___x_1384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1383_);
v___x_1385_ = l_Lean_Syntax_isOfKind(v_v_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec(v_v_1383_);
lean_dec_ref(v_bs_1380_);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = l_Lean_Syntax_getArg(v_v_1383_, v___x_1387_);
v___x_1389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1390_ = l_Lean_Syntax_isOfKind(v___x_1388_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
lean_dec(v_v_1383_);
lean_dec_ref(v_bs_1380_);
v___x_1391_ = lean_box(0);
return v___x_1391_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_bs_x27_1394_; lean_object* v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1392_ = lean_unsigned_to_nat(3u);
v___x_1393_ = lean_unsigned_to_nat(0u);
v_bs_x27_1394_ = lean_array_uset(v_bs_1380_, v_i_1379_, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_getArg(v_v_1383_, v___x_1392_);
lean_dec(v_v_1383_);
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1379_, v___x_1396_);
v___x_1398_ = lean_array_uset(v_bs_x27_1394_, v_i_1379_, v___x_1395_);
v_i_1379_ = v___x_1397_;
v_bs_1380_ = v___x_1398_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_bs_1402_){
_start:
{
size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1403_, v_i_boxed_1404_, v_bs_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1412_, size_t v_i_1413_, lean_object* v_bs_1414_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_lt(v_i_1413_, v_sz_1412_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_bs_1414_);
return v___x_1416_;
}
else
{
lean_object* v_v_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_v_1417_ = lean_array_uget(v_bs_1414_, v_i_1413_);
v___x_1418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1417_);
v___x_1419_ = l_Lean_Syntax_isOfKind(v_v_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_v_1417_);
lean_dec_ref(v_bs_1414_);
v___x_1420_ = lean_box(0);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; lean_object* v_bs_x27_1422_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v_bs_x27_1422_ = lean_array_uset(v_bs_1414_, v_i_1413_, v___x_1421_);
v___x_1429_ = l_Lean_Syntax_getArg(v_v_1417_, v___x_1421_);
lean_dec(v_v_1417_);
v___x_1430_ = l_Lean_Syntax_isNone(v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(2u);
v___x_1432_ = l_Lean_Syntax_matchesNull(v___x_1429_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref(v_bs_x27_1422_);
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
else
{
goto v___jp_1423_;
}
}
else
{
lean_dec(v___x_1429_);
goto v___jp_1423_;
}
v___jp_1423_:
{
lean_object* v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_i_1413_, v___x_1425_);
v___x_1427_ = lean_array_uset(v_bs_x27_1422_, v_i_1413_, v___x_1424_);
v_i_1413_ = v___x_1426_;
v_bs_1414_ = v___x_1427_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1434_, lean_object* v_i_1435_, lean_object* v_bs_1436_){
_start:
{
size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1434_);
lean_dec(v_sz_1434_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1437_, v_i_boxed_1438_, v_bs_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1440_, size_t v_i_1441_, lean_object* v_bs_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_usize_dec_lt(v_i_1441_, v_sz_1440_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_bs_1442_);
return v___x_1444_;
}
else
{
lean_object* v_v_1445_; lean_object* v___x_1446_; lean_object* v_bs_x27_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; 
v_v_1445_ = lean_array_uget(v_bs_1442_, v_i_1441_);
v___x_1446_ = lean_unsigned_to_nat(0u);
v_bs_x27_1447_ = lean_array_uset(v_bs_1442_, v_i_1441_, v___x_1446_);
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_add(v_i_1441_, v___x_1448_);
v___x_1450_ = lean_array_uset(v_bs_x27_1447_, v_i_1441_, v_v_1445_);
v_i_1441_ = v___x_1449_;
v_bs_1442_ = v___x_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1452_, lean_object* v_i_1453_, lean_object* v_bs_1454_){
_start:
{
size_t v_sz_boxed_1455_; size_t v_i_boxed_1456_; lean_object* v_res_1457_; 
v_sz_boxed_1455_ = lean_unbox_usize(v_sz_1452_);
lean_dec(v_sz_1452_);
v_i_boxed_1456_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1455_, v_i_boxed_1456_, v_bs_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1458_, lean_object* v_x_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1459_, v___y_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1463_, v_x_1464_, v___y_1465_, v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec_ref(v_x_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1471_, lean_object* v_as_x27_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
if (lean_obj_tag(v_as_x27_1472_) == 0)
{
lean_object* v___x_1481_; 
lean_dec(v_stx_1471_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_b_1473_);
return v___x_1481_;
}
else
{
lean_object* v_head_1482_; lean_object* v_tail_1483_; lean_object* v_value_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v_b_1473_);
v_head_1482_ = lean_ctor_get(v_as_x27_1472_, 0);
v_tail_1483_ = lean_ctor_get(v_as_x27_1472_, 1);
v_value_1484_ = lean_ctor_get(v_head_1482_, 1);
v___x_1485_ = lean_box(0);
v___x_1486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1487_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1484_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v_stx_1471_);
v___x_1488_ = lean_apply_8(v_value_1484_, v_stx_1471_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, lean_box(0));
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_stx_1471_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1498_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1498_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_a_1489_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1485_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1494_);
v___x_1496_ = v___x_1491_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1520_; 
v_a_1499_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1501_ = v___x_1488_;
v_isShared_1502_ = v_isSharedCheck_1520_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1488_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1520_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint8_t v___x_1503_; 
v___x_1503_ = l_Lean_Exception_isInterrupt(v_a_1499_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
lean_inc(v_a_1499_);
v___x_1504_ = l_Lean_Exception_isRuntime(v_a_1499_);
if (v___x_1504_ == 0)
{
if (lean_obj_tag(v_a_1499_) == 0)
{
lean_object* v___x_1506_; 
lean_dec(v_stx_1471_);
if (v_isShared_1502_ == 0)
{
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1499_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
else
{
lean_object* v_id_1508_; uint8_t v___x_1509_; 
v_id_1508_ = lean_ctor_get(v_a_1499_, 0);
v___x_1509_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1487_, v_id_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; 
lean_dec(v_stx_1471_);
if (v_isShared_1502_ == 0)
{
v___x_1511_ = v___x_1501_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1499_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
lean_dec_ref_known(v_a_1499_, 2);
lean_del_object(v___x_1501_);
v_as_x27_1472_ = v_tail_1483_;
v_b_1473_ = v___x_1486_;
goto _start;
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_stx_1471_);
if (v_isShared_1502_ == 0)
{
v___x_1515_ = v___x_1501_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1499_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_stx_1471_);
if (v_isShared_1502_ == 0)
{
v___x_1518_ = v___x_1501_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1499_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1521_, lean_object* v_as_x27_1522_, lean_object* v_b_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1521_, v_as_x27_1522_, v_b_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v_as_x27_1522_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1534_, lean_object* v_rhs_x3f_1535_, lean_object* v_otherwise_x3f_1536_, lean_object* v_body_x3f_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___y_1546_; uint8_t v___y_1547_; uint8_t v___y_1548_; uint8_t v___y_1549_; uint8_t v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v_body_1557_; lean_object* v___y_1575_; lean_object* v_otherwise_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v_rhs_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; 
if (lean_obj_tag(v_rhs_x3f_1535_) == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1588_ = v___x_1599_;
v___y_1589_ = v_a_1538_;
v___y_1590_ = v_a_1539_;
v___y_1591_ = v_a_1540_;
v___y_1592_ = v_a_1541_;
v___y_1593_ = v_a_1542_;
v___y_1594_ = v_a_1543_;
goto v___jp_1587_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1601_; 
v_val_1600_ = lean_ctor_get(v_rhs_x3f_1535_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_rhs_x3f_1535_, 1);
v___x_1601_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1600_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v_rhs_1588_ = v_a_1602_;
v___y_1589_ = v_a_1538_;
v___y_1590_ = v_a_1539_;
v___y_1591_ = v_a_1540_;
v___y_1592_ = v_a_1541_;
v___y_1593_ = v_a_1542_;
v___y_1594_ = v_a_1543_;
goto v___jp_1587_;
}
else
{
lean_dec(v_body_x3f_1537_);
lean_dec(v_otherwise_x3f_1536_);
lean_dec_ref(v_reassigned_1534_);
return v___x_1601_;
}
}
v___jp_1545_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1552_, 0, v___y_1546_);
lean_ctor_set(v___x_1552_, 1, v___y_1551_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*2, v___y_1549_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*2 + 1, v___y_1547_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*2 + 2, v___y_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*2 + 3, v___y_1548_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
v___jp_1554_:
{
lean_object* v___x_1558_; lean_object* v_info_1559_; uint8_t v_breaks_1560_; uint8_t v_continues_1561_; uint8_t v_returnsEarly_1562_; lean_object* v_numRegularExits_1563_; uint8_t v_noFallthrough_1564_; lean_object* v_reassigns_1565_; size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1558_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1557_, v___y_1556_);
v_info_1559_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1555_, v___x_1558_);
v_breaks_1560_ = lean_ctor_get_uint8(v_info_1559_, sizeof(void*)*2);
v_continues_1561_ = lean_ctor_get_uint8(v_info_1559_, sizeof(void*)*2 + 1);
v_returnsEarly_1562_ = lean_ctor_get_uint8(v_info_1559_, sizeof(void*)*2 + 2);
v_numRegularExits_1563_ = lean_ctor_get(v_info_1559_, 0);
lean_inc(v_numRegularExits_1563_);
v_noFallthrough_1564_ = lean_ctor_get_uint8(v_info_1559_, sizeof(void*)*2 + 3);
v_reassigns_1565_ = lean_ctor_get(v_info_1559_, 1);
lean_inc(v_reassigns_1565_);
lean_dec_ref(v_info_1559_);
v_sz_1566_ = lean_array_size(v_reassigned_1534_);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1566_, v___x_1567_, v_reassigned_1534_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_get_size(v___x_1568_);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec_ref(v___x_1568_);
v___y_1546_ = v_numRegularExits_1563_;
v___y_1547_ = v_continues_1561_;
v___y_1548_ = v_noFallthrough_1564_;
v___y_1549_ = v_breaks_1560_;
v___y_1550_ = v_returnsEarly_1562_;
v___y_1551_ = v_reassigns_1565_;
goto v___jp_1545_;
}
else
{
size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_usize_of_nat(v___x_1570_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1568_, v___x_1567_, v___x_1572_, v_reassigns_1565_);
lean_dec_ref(v___x_1568_);
v___y_1546_ = v_numRegularExits_1563_;
v___y_1547_ = v_continues_1561_;
v___y_1548_ = v_noFallthrough_1564_;
v___y_1549_ = v_breaks_1560_;
v___y_1550_ = v_returnsEarly_1562_;
v___y_1551_ = v___x_1573_;
goto v___jp_1545_;
}
}
v___jp_1574_:
{
if (lean_obj_tag(v_body_x3f_1537_) == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1555_ = v___y_1575_;
v___y_1556_ = v_otherwise_1576_;
v_body_1557_ = v___x_1583_;
goto v___jp_1554_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1585_; 
v_val_1584_ = lean_ctor_get(v_body_x3f_1537_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_body_x3f_1537_, 1);
v___x_1585_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1584_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___y_1555_ = v___y_1575_;
v___y_1556_ = v_otherwise_1576_;
v_body_1557_ = v_a_1586_;
goto v___jp_1554_;
}
else
{
lean_dec_ref(v_otherwise_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v_reassigned_1534_);
return v___x_1585_;
}
}
}
v___jp_1587_:
{
if (lean_obj_tag(v_otherwise_x3f_1536_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1575_ = v_rhs_1588_;
v_otherwise_1576_ = v___x_1595_;
v___y_1577_ = v___y_1589_;
v___y_1578_ = v___y_1590_;
v___y_1579_ = v___y_1591_;
v___y_1580_ = v___y_1592_;
v___y_1581_ = v___y_1593_;
v___y_1582_ = v___y_1594_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1596_; lean_object* v___x_1597_; 
v_val_1596_ = lean_ctor_get(v_otherwise_x3f_1536_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_otherwise_x3f_1536_, 1);
v___x_1597_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1596_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v___y_1575_ = v_rhs_1588_;
v_otherwise_1576_ = v_a_1598_;
v___y_1577_ = v___y_1589_;
v___y_1578_ = v___y_1590_;
v___y_1579_ = v___y_1591_;
v___y_1580_ = v___y_1592_;
v___y_1581_ = v___y_1593_;
v___y_1582_ = v___y_1594_;
goto v___jp_1574_;
}
else
{
lean_dec_ref(v_rhs_1588_);
lean_dec(v_body_x3f_1537_);
lean_dec_ref(v_reassigned_1534_);
return v___x_1597_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1705_, lean_object* v_decl_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v_reassigns_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1706_);
v___x_1743_ = l_Lean_Syntax_isOfKind(v_decl_1706_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1706_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v_decl_1706_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1746_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1747_ = lean_box(0);
v___x_1748_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1747_, v___x_1745_);
v___x_1749_ = l_Std_Format_defWidth;
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = l_Std_Format_pretty(v___x_1748_, v___x_1749_, v___x_1750_, v___x_1750_);
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1746_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1753_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v_pattern_1756_; lean_object* v___y_1758_; lean_object* v_otherwise_x3f_1759_; lean_object* v_body_x3f_x3f_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v_body_x3f_x3f_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v_pattern_1756_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1755_);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1829_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1790_);
v___x_1830_ = l_Lean_Syntax_isNone(v___x_1829_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
lean_inc(v___x_1829_);
v___x_1831_ = l_Lean_Syntax_matchesNull(v___x_1829_, v___x_1790_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v___x_1829_);
lean_dec(v_pattern_1756_);
v___x_1832_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1833_ = lean_box(0);
v___x_1834_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1833_, v___x_1831_);
v___x_1835_ = l_Std_Format_defWidth;
v___x_1836_ = l_Std_Format_pretty(v___x_1834_, v___x_1835_, v___x_1755_, v___x_1755_);
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1832_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1838_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = l_Lean_Syntax_getArg(v___x_1829_, v___x_1755_);
lean_dec(v___x_1829_);
v___x_1841_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1842_ = l_Lean_Syntax_isOfKind(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec(v_pattern_1756_);
v___x_1843_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1844_, v___x_1842_);
v___x_1846_ = l_Std_Format_defWidth;
v___x_1847_ = l_Std_Format_pretty(v___x_1845_, v___x_1846_, v___x_1755_, v___x_1755_);
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1843_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1849_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1850_;
}
else
{
v___y_1792_ = v_a_1707_;
v___y_1793_ = v_a_1708_;
v___y_1794_ = v_a_1709_;
v___y_1795_ = v_a_1710_;
v___y_1796_ = v_a_1711_;
v___y_1797_ = v_a_1712_;
goto v___jp_1791_;
}
}
}
else
{
lean_dec(v___x_1829_);
v___y_1792_ = v_a_1707_;
v___y_1793_ = v_a_1708_;
v___y_1794_ = v_a_1709_;
v___y_1795_ = v_a_1710_;
v___y_1796_ = v_a_1711_;
v___y_1797_ = v_a_1712_;
goto v___jp_1791_;
}
v___jp_1757_:
{
if (v_reassignment_1705_ == 0)
{
lean_object* v___x_1767_; 
lean_dec(v_pattern_1756_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1727_ = v_body_x3f_x3f_1760_;
v___y_1728_ = v_otherwise_x3f_1759_;
v___y_1729_ = v___y_1758_;
v_reassigns_1730_ = v___x_1767_;
v___y_1731_ = v___y_1761_;
v___y_1732_ = v___y_1762_;
v___y_1733_ = v___y_1763_;
v___y_1734_ = v___y_1764_;
v___y_1735_ = v___y_1765_;
v___y_1736_ = v___y_1766_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1756_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___y_1727_ = v_body_x3f_x3f_1760_;
v___y_1728_ = v_otherwise_x3f_1759_;
v___y_1729_ = v___y_1758_;
v_reassigns_1730_ = v_a_1769_;
v___y_1731_ = v___y_1761_;
v___y_1732_ = v___y_1762_;
v___y_1733_ = v___y_1763_;
v___y_1734_ = v___y_1764_;
v___y_1735_ = v___y_1765_;
v___y_1736_ = v___y_1766_;
goto v___jp_1726_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_body_x3f_x3f_1760_);
lean_dec(v_otherwise_x3f_1759_);
lean_dec(v___y_1758_);
v_a_1770_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1768_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
v___jp_1778_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___y_1780_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_body_x3f_x3f_1781_);
v___y_1758_ = v___y_1779_;
v_otherwise_x3f_1759_ = v___x_1788_;
v_body_x3f_x3f_1760_ = v___x_1789_;
v___y_1761_ = v___y_1782_;
v___y_1762_ = v___y_1783_;
v___y_1763_ = v___y_1784_;
v___y_1764_ = v___y_1785_;
v___y_1765_ = v___y_1786_;
v___y_1766_ = v___y_1787_;
goto v___jp_1757_;
}
v___jp_1791_:
{
lean_object* v___x_1798_; lean_object* v_rhs_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1798_ = lean_unsigned_to_nat(3u);
v_rhs_1799_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1798_);
v___x_1800_ = lean_unsigned_to_nat(4u);
v___x_1801_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1800_);
v___x_1802_ = l_Lean_Syntax_isNone(v___x_1801_);
if (v___x_1802_ == 0)
{
uint8_t v___x_1803_; 
lean_inc(v___x_1801_);
v___x_1803_ = l_Lean_Syntax_matchesNull(v___x_1801_, v___x_1798_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v___x_1801_);
lean_dec(v_rhs_1799_);
lean_dec(v_pattern_1756_);
v___x_1804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1805_ = lean_box(0);
v___x_1806_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1805_, v___x_1803_);
v___x_1807_ = l_Std_Format_defWidth;
v___x_1808_ = l_Std_Format_pretty(v___x_1806_, v___x_1807_, v___x_1755_, v___x_1755_);
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1804_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1810_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v_otherwise_x3f_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1812_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1813_ = l_Lean_Syntax_getArg(v___x_1801_, v___x_1790_);
v___x_1814_ = l_Lean_Syntax_getArg(v___x_1801_, v___x_1812_);
lean_dec(v___x_1801_);
v___x_1815_ = l_Lean_Syntax_isNone(v___x_1814_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; 
lean_inc(v___x_1814_);
v___x_1816_ = l_Lean_Syntax_matchesNull(v___x_1814_, v___x_1790_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___x_1814_);
lean_dec(v_otherwise_x3f_1813_);
lean_dec(v_rhs_1799_);
lean_dec(v_pattern_1756_);
v___x_1817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1818_, v___x_1816_);
v___x_1820_ = l_Std_Format_defWidth;
v___x_1821_ = l_Std_Format_pretty(v___x_1819_, v___x_1820_, v___x_1755_, v___x_1755_);
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1817_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1823_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1824_;
}
else
{
lean_object* v_body_x3f_x3f_1825_; lean_object* v___x_1826_; 
lean_dec(v_decl_1706_);
v_body_x3f_x3f_1825_ = l_Lean_Syntax_getArg(v___x_1814_, v___x_1755_);
lean_dec(v___x_1814_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_body_x3f_x3f_1825_);
v___y_1779_ = v_rhs_1799_;
v___y_1780_ = v_otherwise_x3f_1813_;
v_body_x3f_x3f_1781_ = v___x_1826_;
v___y_1782_ = v___y_1792_;
v___y_1783_ = v___y_1793_;
v___y_1784_ = v___y_1794_;
v___y_1785_ = v___y_1795_;
v___y_1786_ = v___y_1796_;
v___y_1787_ = v___y_1797_;
goto v___jp_1778_;
}
}
else
{
lean_object* v___x_1827_; 
lean_dec(v___x_1814_);
lean_dec(v_decl_1706_);
v___x_1827_ = lean_box(0);
v___y_1779_ = v_rhs_1799_;
v___y_1780_ = v_otherwise_x3f_1813_;
v_body_x3f_x3f_1781_ = v___x_1827_;
v___y_1782_ = v___y_1792_;
v___y_1783_ = v___y_1793_;
v___y_1784_ = v___y_1794_;
v___y_1785_ = v___y_1795_;
v___y_1786_ = v___y_1796_;
v___y_1787_ = v___y_1797_;
goto v___jp_1778_;
}
}
}
else
{
lean_object* v___x_1828_; 
lean_dec(v___x_1801_);
lean_dec(v_decl_1706_);
v___x_1828_ = lean_box(0);
v___y_1758_ = v_rhs_1799_;
v_otherwise_x3f_1759_ = v___x_1828_;
v_body_x3f_x3f_1760_ = v___x_1828_;
v___y_1761_ = v___y_1792_;
v___y_1762_ = v___y_1793_;
v___y_1763_ = v___y_1794_;
v___y_1764_ = v___y_1795_;
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
goto v___jp_1757_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v_x_1852_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v_x_1852_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1851_);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1852_);
v___x_1867_ = l_Lean_Syntax_isOfKind(v_x_1852_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_x_1852_);
v___x_1868_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1869_ = lean_box(0);
v___x_1870_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1869_, v___x_1867_);
v___x_1871_ = l_Std_Format_defWidth;
v___x_1872_ = l_Std_Format_pretty(v___x_1870_, v___x_1871_, v___x_1851_, v___x_1851_);
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1868_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1874_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1876_);
v___x_1878_ = l_Lean_Syntax_isNone(v___x_1877_);
if (v___x_1878_ == 0)
{
uint8_t v___x_1879_; 
lean_inc(v___x_1877_);
v___x_1879_ = l_Lean_Syntax_matchesNull(v___x_1877_, v___x_1876_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v___x_1877_);
lean_dec(v_x_1852_);
v___x_1880_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1881_ = lean_box(0);
v___x_1882_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1881_, v___x_1879_);
v___x_1883_ = l_Std_Format_defWidth;
v___x_1884_ = l_Std_Format_pretty(v___x_1882_, v___x_1883_, v___x_1851_, v___x_1851_);
v___x_1885_ = l_Lean_stringToMessageData(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1880_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1886_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = l_Lean_Syntax_getArg(v___x_1877_, v___x_1851_);
lean_dec(v___x_1877_);
v___x_1889_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1890_ = l_Lean_Syntax_isOfKind(v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_x_1852_);
v___x_1891_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Lean_Syntax_formatStx(v_decl_1706_, v___x_1892_, v___x_1890_);
v___x_1894_ = l_Std_Format_defWidth;
v___x_1895_ = l_Std_Format_pretty(v___x_1893_, v___x_1894_, v___x_1851_, v___x_1851_);
v___x_1896_ = l_Lean_stringToMessageData(v___x_1895_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1891_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1897_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1898_;
}
else
{
v___y_1854_ = v_a_1707_;
v___y_1855_ = v_a_1708_;
v___y_1856_ = v_a_1709_;
v___y_1857_ = v_a_1710_;
v___y_1858_ = v_a_1711_;
v___y_1859_ = v_a_1712_;
goto v___jp_1853_;
}
}
}
else
{
lean_dec(v___x_1877_);
v___y_1854_ = v_a_1707_;
v___y_1855_ = v_a_1708_;
v___y_1856_ = v_a_1709_;
v___y_1857_ = v_a_1710_;
v___y_1858_ = v_a_1711_;
v___y_1859_ = v_a_1712_;
goto v___jp_1853_;
}
}
v___jp_1853_:
{
lean_object* v___x_1860_; lean_object* v_rhs_1861_; 
v___x_1860_ = lean_unsigned_to_nat(3u);
v_rhs_1861_ = l_Lean_Syntax_getArg(v_decl_1706_, v___x_1860_);
lean_dec(v_decl_1706_);
if (v_reassignment_1705_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v_x_1852_);
v___x_1862_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1715_ = v___y_1857_;
v___y_1716_ = v___y_1855_;
v___y_1717_ = v___y_1854_;
v___y_1718_ = v_rhs_1861_;
v___y_1719_ = v___y_1856_;
v___y_1720_ = v___y_1858_;
v___y_1721_ = v___y_1859_;
v___y_1722_ = v___x_1862_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(1u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_array_push(v___x_1864_, v_x_1852_);
v___y_1715_ = v___y_1857_;
v___y_1716_ = v___y_1855_;
v___y_1717_ = v___y_1854_;
v___y_1718_ = v_rhs_1861_;
v___y_1719_ = v___y_1856_;
v___y_1720_ = v___y_1858_;
v___y_1721_ = v___y_1859_;
v___y_1722_ = v___x_1865_;
goto v___jp_1714_;
}
}
}
v___jp_1714_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___y_1718_);
v___x_1724_ = lean_box(0);
v___x_1725_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1722_, v___x_1723_, v___x_1724_, v___x_1724_, v___y_1717_, v___y_1716_, v___y_1719_, v___y_1715_, v___y_1720_, v___y_1721_);
return v___x_1725_;
}
v___jp_1726_:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1729_);
if (lean_obj_tag(v___y_1727_) == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1730_, v___x_1737_, v___y_1728_, v___x_1738_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; lean_object* v___x_1741_; 
v_val_1740_ = lean_ctor_get(v___y_1727_, 0);
lean_inc(v_val_1740_);
lean_dec_ref_known(v___y_1727_, 1);
v___x_1741_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1730_, v___x_1737_, v___y_1728_, v_val_1740_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_2024_, size_t v_sz_2025_, size_t v_i_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2026_, v_sz_2025_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2027_);
return v___x_2036_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_array_uget_borrowed(v_as_2024_, v_i_2026_);
lean_inc(v_a_2037_);
v___x_2038_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_2037_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2039_, v_b_2027_);
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2026_, v___x_2041_);
v_i_2026_ = v___x_2042_;
v_b_2027_ = v___x_2040_;
goto _start;
}
else
{
lean_dec_ref(v_b_2027_);
return v___x_2038_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2073_, lean_object* v_as_2074_, size_t v_sz_2075_, size_t v_i_2076_, lean_object* v_b_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_a_2086_; uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2076_, v_sz_2075_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_b_2077_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v_a_2093_; uint8_t v___x_2094_; 
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2093_ = lean_array_uget_borrowed(v_as_2074_, v_i_2076_);
lean_inc(v_a_2093_);
v___x_2094_ = l_Lean_Syntax_isOfKind(v_a_2093_, v___x_2092_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
v_a_2086_ = v_b_2077_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_b_2077_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2104_ = lean_unsigned_to_nat(3u);
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = l_Lean_Syntax_getArg(v_a_2093_, v___x_2123_);
v___x_2125_ = l_Lean_Syntax_getArgs(v___x_2124_);
lean_dec(v___x_2124_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2128_ = lean_array_get_size(v___x_2125_);
v___x_2129_ = lean_nat_dec_lt(v___x_2126_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_dec_ref(v___x_2125_);
v___y_2106_ = v___x_2127_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; lean_object* v___x_2134_; lean_object* v_snd_2135_; 
v___x_2130_ = lean_box(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2127_);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_of_nat(v___x_2128_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2094_, v___x_2073_, v___x_2125_, v___x_2132_, v___x_2133_, v___x_2131_);
lean_dec_ref(v___x_2125_);
v_snd_2135_ = lean_ctor_get(v___x_2134_, 1);
lean_inc(v_snd_2135_);
lean_dec_ref(v___x_2134_);
v___y_2106_ = v_snd_2135_;
goto v___jp_2105_;
}
v___jp_2105_:
{
size_t v_sz_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v_sz_2107_ = lean_array_size(v___y_2106_);
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2107_, v___x_2108_, v___y_2106_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref_known(v___x_2110_, 1);
v_a_2086_ = v_b_2077_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_b_2077_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref_known(v___x_2109_, 1);
v___x_2119_ = l_Lean_Syntax_getArg(v_a_2093_, v___x_2104_);
v___x_2120_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2119_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2077_, v_a_2121_);
v_a_2086_ = v___x_2122_;
goto v___jp_2085_;
}
else
{
lean_dec_ref(v_b_2077_);
return v___x_2120_;
}
}
}
}
}
v___jp_2085_:
{
size_t v___x_2087_; size_t v___x_2088_; 
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2076_, v___x_2087_);
v_i_2076_ = v___x_2088_;
v_b_2077_ = v_a_2086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2136_, size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_a_2148_; uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_b_2139_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v_a_2155_ = lean_array_uget_borrowed(v_as_2136_, v_i_2138_);
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2155_);
v___x_2169_ = l_Lean_Syntax_isOfKind(v_a_2155_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2155_);
v___x_2171_ = l_Lean_Syntax_isOfKind(v_a_2155_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2172_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2173_ = lean_box(0);
lean_inc(v_a_2155_);
v___x_2174_ = l_Lean_Syntax_formatStx(v_a_2155_, v___x_2173_, v___x_2171_);
v___x_2175_ = l_Std_Format_defWidth;
v___x_2176_ = l_Std_Format_pretty(v___x_2174_, v___x_2175_, v___x_2154_, v___x_2154_);
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2172_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2178_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_dec_ref_known(v___x_2179_, 1);
v_a_2148_ = v_b_2139_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_b_2139_);
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
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = l_Lean_Syntax_getArg(v_a_2155_, v___x_2188_);
v___x_2190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2189_);
v___x_2191_ = l_Lean_Syntax_isOfKind(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v___x_2189_);
v___x_2192_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2193_ = lean_box(0);
lean_inc(v_a_2155_);
v___x_2194_ = l_Lean_Syntax_formatStx(v_a_2155_, v___x_2193_, v___x_2191_);
v___x_2195_ = l_Std_Format_defWidth;
v___x_2196_ = l_Std_Format_pretty(v___x_2194_, v___x_2195_, v___x_2154_, v___x_2154_);
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2192_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2198_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_dec_ref_known(v___x_2199_, 1);
v_a_2148_ = v_b_2139_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v_b_2139_);
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2208_ = l_Lean_Syntax_getArg(v___x_2189_, v___x_2154_);
lean_dec(v___x_2189_);
v___x_2209_ = l_Lean_Syntax_getArgs(v___x_2208_);
lean_dec(v___x_2208_);
v_sz_2210_ = lean_array_size(v___x_2209_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2169_, v___x_2209_, v_sz_2210_, v___x_2211_, v_b_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec_ref(v___x_2209_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v_a_2148_ = v_a_2213_;
goto v___jp_2147_;
}
else
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = lean_unsigned_to_nat(2u);
v___x_2215_ = l_Lean_Syntax_getArg(v_a_2155_, v___x_2214_);
v___x_2216_ = l_Lean_Syntax_isNone(v___x_2215_);
if (v___x_2216_ == 0)
{
uint8_t v___x_2217_; 
v___x_2217_ = l_Lean_Syntax_matchesNull(v___x_2215_, v___x_2214_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2219_ = lean_box(0);
lean_inc(v_a_2155_);
v___x_2220_ = l_Lean_Syntax_formatStx(v_a_2155_, v___x_2219_, v___x_2217_);
v___x_2221_ = l_Std_Format_defWidth;
v___x_2222_ = l_Std_Format_pretty(v___x_2220_, v___x_2221_, v___x_2154_, v___x_2154_);
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2218_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2224_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_dec_ref_known(v___x_2225_, 1);
v_a_2148_ = v_b_2139_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_b_2139_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
v___y_2157_ = v___y_2140_;
v___y_2158_ = v___y_2141_;
v___y_2159_ = v___y_2142_;
v___y_2160_ = v___y_2143_;
v___y_2161_ = v___y_2144_;
v___y_2162_ = v___y_2145_;
goto v___jp_2156_;
}
}
else
{
lean_dec(v___x_2215_);
v___y_2157_ = v___y_2140_;
v___y_2158_ = v___y_2141_;
v___y_2159_ = v___y_2142_;
v___y_2160_ = v___y_2143_;
v___y_2161_ = v___y_2144_;
v___y_2162_ = v___y_2145_;
goto v___jp_2156_;
}
}
v___jp_2156_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_unsigned_to_nat(4u);
v___x_2164_ = l_Lean_Syntax_getArg(v_a_2155_, v___x_2163_);
v___x_2165_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2164_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2166_, v_b_2139_);
v_a_2148_ = v___x_2167_;
goto v___jp_2147_;
}
else
{
lean_dec_ref(v_b_2139_);
return v___x_2165_;
}
}
}
v___jp_2147_:
{
size_t v___x_2149_; size_t v___x_2150_; 
v___x_2149_ = ((size_t)1ULL);
v___x_2150_ = lean_usize_add(v_i_2138_, v___x_2149_);
v_i_2138_ = v___x_2150_;
v_b_2139_ = v_a_2148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2234_) == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2245_; 
v_val_2244_ = lean_ctor_get(v_stx_x3f_2234_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v_stx_x3f_2234_, 1);
v___x_2245_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2244_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2264_, lean_object* v_as_2265_, size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_a_2277_; uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_lt(v_i_2267_, v_sz_2266_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_b_2268_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v_a_2284_; uint8_t v___x_2285_; 
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2284_ = lean_array_uget_borrowed(v_as_2265_, v_i_2267_);
lean_inc(v_a_2284_);
v___x_2285_ = l_Lean_Syntax_isOfKind(v_a_2284_, v___x_2283_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_dec_ref_known(v___x_2286_, 1);
v_a_2277_ = v_b_2268_;
goto v___jp_2276_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_b_2268_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___y_2297_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2295_ = lean_unsigned_to_nat(3u);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = l_Lean_Syntax_getArg(v_a_2284_, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_getArgs(v___x_2315_);
lean_dec(v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2319_ = lean_array_get_size(v___x_2316_);
v___x_2320_ = lean_nat_dec_lt(v___x_2317_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec_ref(v___x_2316_);
v___y_2297_ = v___x_2318_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; lean_object* v_snd_2326_; 
v___x_2321_ = lean_box(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2318_);
v___x_2323_ = ((size_t)0ULL);
v___x_2324_ = lean_usize_of_nat(v___x_2319_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2285_, v___x_2264_, v___x_2316_, v___x_2323_, v___x_2324_, v___x_2322_);
lean_dec_ref(v___x_2316_);
v_snd_2326_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_snd_2326_);
lean_dec_ref(v___x_2325_);
v___y_2297_ = v_snd_2326_;
goto v___jp_2296_;
}
v___jp_2296_:
{
size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v_sz_2298_ = lean_array_size(v___y_2297_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2298_, v___x_2299_, v___y_2297_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_dec_ref_known(v___x_2301_, 1);
v_a_2277_ = v_b_2268_;
goto v___jp_2276_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_b_2268_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2310_ = l_Lean_Syntax_getArg(v_a_2284_, v___x_2295_);
v___x_2311_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2310_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2268_, v_a_2312_);
v_a_2277_ = v___x_2313_;
goto v___jp_2276_;
}
else
{
lean_dec_ref(v_b_2268_);
return v___x_2311_;
}
}
}
}
}
v___jp_2276_:
{
size_t v___x_2278_; size_t v___x_2279_; 
v___x_2278_ = ((size_t)1ULL);
v___x_2279_ = lean_usize_add(v_i_2267_, v___x_2278_);
v_i_2267_ = v___x_2279_;
v_b_2268_ = v_a_2277_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2375_ = l_Lean_NameSet_empty;
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = 0;
v___x_2378_ = 1;
v___x_2379_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2379_, 0, v___x_2376_);
lean_ctor_set(v___x_2379_, 1, v___x_2375_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2, v___x_2378_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2 + 1, v___x_2377_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2 + 2, v___x_2377_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*2 + 3, v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___y_2389_; lean_object* v_bodyInfo_2390_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2410_; lean_object* v_bodyInfo_2411_; lean_object* v___x_2414_; lean_object* v_env_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = lean_st_ref_get(v_a_2386_);
v_env_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_env_2415_);
lean_dec(v___x_2414_);
lean_inc(v_stx_2380_);
v___x_2416_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2416_, 0, v_env_2415_);
lean_closure_set(v___x_2416_, 1, v_stx_2380_);
v___x_2417_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2416_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_5123_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_5123_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_5123_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
if (lean_obj_tag(v_a_2418_) == 1)
{
lean_object* v_val_2422_; lean_object* v_snd_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_del_object(v___x_2420_);
lean_dec(v_stx_2380_);
v_val_2422_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_val_2422_);
lean_dec_ref_known(v_a_2418_, 1);
v_snd_2423_ = lean_ctor_get(v_val_2422_, 1);
lean_inc(v_snd_2423_);
lean_dec(v_val_2422_);
v___x_2424_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2424_, 0, lean_box(0));
lean_closure_set(v___x_2424_, 1, v_snd_2423_);
v___x_2425_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2424_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v_stx_2380_ = v_a_2426_;
goto _start;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2425_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2425_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___x_2618_; uint8_t v___x_2619_; uint8_t v___x_2620_; 
lean_dec(v_a_2418_);
v___x_2618_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2380_);
v___x_2619_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2618_);
v___x_2620_ = 1;
if (v___x_2619_ == 0)
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2380_);
v___x_2622_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2380_);
v___x_2624_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2380_);
v___x_2626_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2380_);
v___x_2628_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2380_);
v___x_2630_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
lean_del_object(v___x_2420_);
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2380_);
v___x_2632_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2380_);
v___x_2634_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; 
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2380_);
v___x_2636_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2380_);
v___x_2698_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2380_);
v___x_2700_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2380_);
v___x_2702_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2380_);
v___x_2704_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2380_);
v___x_2706_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2380_);
v___x_2708_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2380_);
v___x_2710_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___y_2714_; uint8_t v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2717_; 
v___x_2711_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2380_);
v___x_2712_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2380_);
v___x_2721_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2380_);
v___x_2723_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2380_);
v___x_2725_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2380_);
v___x_2727_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2380_);
v___x_2729_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2380_);
v___x_2731_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2380_);
v___x_2733_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2380_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2380_);
v___x_2737_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2380_);
v___x_2739_ = l_Lean_Syntax_isOfKind(v_stx_2380_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_env_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc_n(v_stx_2380_, 2);
v___x_2740_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2741_ = lean_st_ref_get(v_a_2386_);
v_env_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_ref(v_env_2742_);
lean_dec(v___x_2741_);
v___x_2743_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2744_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2743_, v_env_2742_, v___x_2740_);
v___x_2745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2746_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2744_, v___x_2745_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2777_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2777_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2777_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_fst_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2775_; 
v_fst_2751_ = lean_ctor_get(v_a_2747_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v_a_2747_, 1);
lean_dec(v_unused_2776_);
v___x_2753_ = v_a_2747_;
v_isShared_2754_ = v_isSharedCheck_2775_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_fst_2751_);
lean_dec(v_a_2747_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2775_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
if (lean_obj_tag(v_fst_2751_) == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
lean_del_object(v___x_2749_);
v___x_2755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2756_ = l_Lean_MessageData_ofName(v___x_2740_);
lean_inc_ref(v___x_2756_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 7);
lean_ctor_set(v___x_2753_, 1, v___x_2756_);
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2758_ = v___x_2753_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2759_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2762_ = l_Lean_indentD(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2756_);
v___x_2767_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2768_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_2769_;
}
}
else
{
lean_object* v_val_2771_; lean_object* v___x_2773_; 
lean_del_object(v___x_2753_);
lean_dec(v___x_2740_);
lean_dec(v_stx_2380_);
v_val_2771_ = lean_ctor_get(v_fst_2751_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v_fst_2751_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_val_2771_);
v___x_2773_ = v___x_2749_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_val_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v___x_2740_);
lean_dec(v_stx_2380_);
v_a_2778_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2746_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2746_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___y_2790_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_unsigned_to_nat(5u);
v___x_2788_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2787_);
v___x_2799_ = lean_unsigned_to_nat(6u);
v___x_2800_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2799_);
lean_dec(v_stx_2380_);
v___x_2801_ = l_Lean_Syntax_getOptional_x3f(v___x_2800_);
lean_dec(v___x_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_box(0);
v___y_2790_ = v___x_2802_;
goto v___jp_2789_;
}
else
{
lean_object* v_val_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_val_2803_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2801_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_val_2803_);
lean_dec(v___x_2801_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_val_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
v___y_2790_ = v___x_2808_;
goto v___jp_2789_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2788_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2791_) == 0)
{
if (lean_obj_tag(v___y_2790_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_NameSet_empty;
v___x_2794_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2794_, 0, v___x_2786_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*2, v___x_2737_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*2 + 1, v___x_2737_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*2 + 2, v___x_2737_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*2 + 3, v___x_2737_);
v___y_2389_ = v_a_2792_;
v_bodyInfo_2390_ = v___x_2794_;
goto v___jp_2388_;
}
else
{
lean_object* v_a_2795_; lean_object* v_val_2796_; lean_object* v___x_2797_; 
v_a_2795_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2791_, 1);
v_val_2796_ = lean_ctor_get(v___y_2790_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___y_2790_, 1);
v___x_2797_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2796_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2389_ = v_a_2795_;
v_bodyInfo_2390_ = v_a_2798_;
goto v___jp_2388_;
}
else
{
lean_dec(v_a_2795_);
return v___x_2797_;
}
}
}
else
{
lean_dec(v___y_2790_);
return v___x_2791_;
}
}
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___y_2815_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = lean_unsigned_to_nat(5u);
v___x_2813_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2812_);
v___x_2824_ = lean_unsigned_to_nat(6u);
v___x_2825_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2824_);
lean_dec(v_stx_2380_);
v___x_2826_ = l_Lean_Syntax_getOptional_x3f(v___x_2825_);
lean_dec(v___x_2825_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_box(0);
v___y_2815_ = v___x_2827_;
goto v___jp_2814_;
}
else
{
lean_object* v_val_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_val_2828_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2826_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_val_2828_);
lean_dec(v___x_2826_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_val_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
v___y_2815_ = v___x_2833_;
goto v___jp_2814_;
}
}
}
v___jp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2813_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2816_) == 0)
{
if (lean_obj_tag(v___y_2815_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = l_Lean_NameSet_empty;
v___x_2819_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2819_, 0, v___x_2811_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*2, v___x_2735_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*2 + 1, v___x_2735_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*2 + 2, v___x_2735_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*2 + 3, v___x_2735_);
v___y_2410_ = v_a_2817_;
v_bodyInfo_2411_ = v___x_2819_;
goto v___jp_2409_;
}
else
{
lean_object* v_a_2820_; lean_object* v_val_2821_; lean_object* v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2816_, 1);
v_val_2821_ = lean_ctor_get(v___y_2815_, 0);
lean_inc(v_val_2821_);
lean_dec_ref_known(v___y_2815_, 1);
v___x_2822_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2821_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___y_2410_ = v_a_2820_;
v_bodyInfo_2411_ = v_a_2823_;
goto v___jp_2409_;
}
else
{
lean_dec(v_a_2820_);
return v___x_2822_;
}
}
}
else
{
lean_dec(v___y_2815_);
return v___x_2816_;
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_unsigned_to_nat(1u);
v___x_3051_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2837_);
v___x_3052_ = l_Lean_Syntax_isNone(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(5u);
v___x_3054_ = l_Lean_Syntax_matchesNull(v___x_3051_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_env_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3055_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3056_ = lean_st_ref_get(v_a_2386_);
v_env_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc_ref(v_env_3057_);
lean_dec(v___x_3056_);
v___x_3058_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3059_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3058_, v_env_3057_, v___x_3055_);
v___x_3060_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3061_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3059_, v___x_3060_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3059_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3092_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3092_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3092_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v_fst_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3090_; 
v_fst_3066_ = lean_ctor_get(v_a_3062_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_a_3062_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v_a_3062_, 1);
lean_dec(v_unused_3091_);
v___x_3068_ = v_a_3062_;
v_isShared_3069_ = v_isSharedCheck_3090_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_fst_3066_);
lean_dec(v_a_3062_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3090_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
if (lean_obj_tag(v_fst_3066_) == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_del_object(v___x_3064_);
v___x_3070_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3071_ = l_Lean_MessageData_ofName(v___x_3055_);
lean_inc_ref(v___x_3071_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set_tag(v___x_3068_, 7);
lean_ctor_set(v___x_3068_, 1, v___x_3071_);
lean_ctor_set(v___x_3068_, 0, v___x_3070_);
v___x_3073_ = v___x_3068_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3074_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3077_ = l_Lean_indentD(v___x_3076_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3075_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v___x_3071_);
v___x_3082_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3083_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3084_;
}
}
else
{
lean_object* v_val_3086_; lean_object* v___x_3088_; 
lean_del_object(v___x_3068_);
lean_dec(v___x_3055_);
lean_dec(v_stx_2380_);
v_val_3086_ = lean_ctor_get(v_fst_3066_, 0);
lean_inc(v_val_3086_);
lean_dec_ref_known(v_fst_3066_, 1);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v_val_3086_);
v___x_3088_ = v___x_3064_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_val_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v___x_3055_);
lean_dec(v_stx_2380_);
v_a_3093_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3061_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3061_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
v___y_2839_ = v_a_2381_;
v___y_2840_ = v_a_2382_;
v___y_2841_ = v_a_2383_;
v___y_2842_ = v_a_2384_;
v___y_2843_ = v_a_2385_;
v___y_2844_ = v_a_2386_;
goto v___jp_2838_;
}
}
else
{
lean_dec(v___x_3051_);
v___y_2839_ = v_a_2381_;
v___y_2840_ = v_a_2382_;
v___y_2841_ = v_a_2383_;
v___y_2842_ = v_a_2384_;
v___y_2843_ = v_a_2385_;
v___y_2844_ = v_a_2386_;
goto v___jp_2838_;
}
v___jp_2838_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_unsigned_to_nat(4u);
v___x_2846_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2845_);
v___x_2847_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2846_);
v___x_2848_ = l_Lean_Syntax_isOfKind(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_env_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v___x_2846_);
lean_inc_n(v_stx_2380_, 2);
v___x_2849_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2850_ = lean_st_ref_get(v___y_2844_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_env_2851_);
lean_dec(v___x_2850_);
v___x_2852_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2853_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2852_, v_env_2851_, v___x_2849_);
v___x_2854_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2855_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2853_, v___x_2854_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___x_2853_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2886_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2886_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2886_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_fst_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2884_; 
v_fst_2860_ = lean_ctor_get(v_a_2856_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_a_2856_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_a_2856_, 1);
lean_dec(v_unused_2885_);
v___x_2862_ = v_a_2856_;
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_fst_2860_);
lean_dec(v_a_2856_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
if (lean_obj_tag(v_fst_2860_) == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_del_object(v___x_2858_);
v___x_2864_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2865_ = l_Lean_MessageData_ofName(v___x_2849_);
lean_inc_ref(v___x_2865_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 7);
lean_ctor_set(v___x_2862_, 1, v___x_2865_);
lean_ctor_set(v___x_2862_, 0, v___x_2864_);
v___x_2867_ = v___x_2862_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2868_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2871_ = l_Lean_indentD(v___x_2870_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2865_);
v___x_2876_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2877_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2878_;
}
}
else
{
lean_object* v_val_2880_; lean_object* v___x_2882_; 
lean_del_object(v___x_2862_);
lean_dec(v___x_2849_);
lean_dec(v_stx_2380_);
v_val_2880_ = lean_ctor_get(v_fst_2860_, 0);
lean_inc(v_val_2880_);
lean_dec_ref_known(v_fst_2860_, 1);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v_val_2880_);
v___x_2882_ = v___x_2858_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_val_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v___x_2849_);
lean_dec(v_stx_2380_);
v_a_2887_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2855_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2855_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; size_t v_sz_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2895_ = l_Lean_Syntax_getArg(v___x_2846_, v___x_2836_);
v___x_2896_ = l_Lean_Syntax_getArgs(v___x_2895_);
lean_dec(v___x_2895_);
v_sz_2897_ = lean_array_size(v___x_2896_);
v___x_2898_ = ((size_t)0ULL);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2897_, v___x_2898_, v___x_2896_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v_env_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v___x_2846_);
lean_inc_n(v_stx_2380_, 2);
v___x_2900_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2901_ = lean_st_ref_get(v___y_2844_);
v_env_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc_ref(v_env_2902_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2904_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2903_, v_env_2902_, v___x_2900_);
v___x_2905_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2906_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2904_, v___x_2905_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___x_2904_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2937_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2937_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2937_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_fst_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2935_; 
v_fst_2911_ = lean_ctor_get(v_a_2907_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_a_2907_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; 
v_unused_2936_ = lean_ctor_get(v_a_2907_, 1);
lean_dec(v_unused_2936_);
v___x_2913_ = v_a_2907_;
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_fst_2911_);
lean_dec(v_a_2907_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
if (lean_obj_tag(v_fst_2911_) == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
lean_del_object(v___x_2909_);
v___x_2915_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2916_ = l_Lean_MessageData_ofName(v___x_2900_);
lean_inc_ref(v___x_2916_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 7);
lean_ctor_set(v___x_2913_, 1, v___x_2916_);
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2919_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2922_ = l_Lean_indentD(v___x_2921_);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2920_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___x_2916_);
v___x_2927_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2928_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2929_;
}
}
else
{
lean_object* v_val_2931_; lean_object* v___x_2933_; 
lean_del_object(v___x_2913_);
lean_dec(v___x_2900_);
lean_dec(v_stx_2380_);
v_val_2931_ = lean_ctor_get(v_fst_2911_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v_fst_2911_, 1);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v_val_2931_);
v___x_2933_ = v___x_2909_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_val_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___x_2900_);
lean_dec(v_stx_2380_);
v_a_2938_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2906_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2906_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_val_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_val_2946_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_val_2946_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2947_ = l_Lean_Syntax_getArg(v___x_2846_, v___x_2837_);
lean_dec(v___x_2846_);
v___x_2948_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_2947_);
v___x_2949_ = l_Lean_Syntax_isOfKind(v___x_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_env_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v___x_2947_);
lean_dec(v_val_2946_);
lean_inc_n(v_stx_2380_, 2);
v___x_2950_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2951_ = lean_st_ref_get(v___y_2844_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_ref(v_env_2952_);
lean_dec(v___x_2951_);
v___x_2953_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2954_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2953_, v_env_2952_, v___x_2950_);
v___x_2955_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2956_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2954_, v___x_2955_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___x_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2987_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2987_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2987_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_fst_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2985_; 
v_fst_2961_ = lean_ctor_get(v_a_2957_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v_a_2957_, 1);
lean_dec(v_unused_2986_);
v___x_2963_ = v_a_2957_;
v_isShared_2964_ = v_isSharedCheck_2985_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_fst_2961_);
lean_dec(v_a_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2985_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
if (lean_obj_tag(v_fst_2961_) == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
lean_del_object(v___x_2959_);
v___x_2965_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2966_ = l_Lean_MessageData_ofName(v___x_2950_);
lean_inc_ref(v___x_2966_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 7);
lean_ctor_set(v___x_2963_, 1, v___x_2966_);
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2969_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2972_ = l_Lean_indentD(v___x_2971_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2970_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2966_);
v___x_2977_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2978_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2979_;
}
}
else
{
lean_object* v_val_2981_; lean_object* v___x_2983_; 
lean_del_object(v___x_2963_);
lean_dec(v___x_2950_);
lean_dec(v_stx_2380_);
v_val_2981_ = lean_ctor_get(v_fst_2961_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v_fst_2961_, 1);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v_val_2981_);
v___x_2983_ = v___x_2959_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_val_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v___x_2950_);
lean_dec(v_stx_2380_);
v_a_2988_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2956_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2956_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = l_Lean_Syntax_getArg(v___x_2947_, v___x_2837_);
v___x_2997_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_2998_ = l_Lean_Syntax_isOfKind(v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_env_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v___x_2947_);
lean_dec(v_val_2946_);
lean_inc_n(v_stx_2380_, 2);
v___x_2999_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3000_ = lean_st_ref_get(v___y_2844_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_3000_);
v___x_3002_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3003_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3002_, v_env_3001_, v___x_2999_);
v___x_3004_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3005_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3003_, v___x_3004_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___x_3003_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3036_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3036_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3036_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v_fst_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3034_; 
v_fst_3010_ = lean_ctor_get(v_a_3006_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_a_3006_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v_a_3006_, 1);
lean_dec(v_unused_3035_);
v___x_3012_ = v_a_3006_;
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_fst_3010_);
lean_dec(v_a_3006_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
if (lean_obj_tag(v_fst_3010_) == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
lean_del_object(v___x_3008_);
v___x_3014_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3015_ = l_Lean_MessageData_ofName(v___x_2999_);
lean_inc_ref(v___x_3015_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 7);
lean_ctor_set(v___x_3012_, 1, v___x_3015_);
lean_ctor_set(v___x_3012_, 0, v___x_3014_);
v___x_3017_ = v___x_3012_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3018_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3021_ = l_Lean_indentD(v___x_3020_);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3019_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3015_);
v___x_3026_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3027_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_3028_;
}
}
else
{
lean_object* v_val_3030_; lean_object* v___x_3032_; 
lean_del_object(v___x_3012_);
lean_dec(v___x_2999_);
lean_dec(v_stx_2380_);
v_val_3030_ = lean_ctor_get(v_fst_3010_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v_fst_3010_, 1);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v_val_3030_);
v___x_3032_ = v___x_3008_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_val_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v___x_2999_);
lean_dec(v_stx_2380_);
v_a_3037_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3005_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3005_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_dec(v_stx_2380_);
v___x_3045_ = lean_unsigned_to_nat(3u);
v___x_3046_ = l_Lean_Syntax_getArg(v___x_2947_, v___x_3045_);
lean_dec(v___x_2947_);
v___x_3047_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3046_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; size_t v_sz_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v_sz_3049_ = lean_array_size(v_val_2946_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2946_, v_sz_3049_, v___x_2898_, v_a_3048_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v_val_2946_);
return v___x_3050_;
}
else
{
lean_dec(v_val_2946_);
return v___x_3047_;
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
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v_stx_2380_);
v___x_3101_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
return v___x_3102_;
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_stx_2380_);
v___x_3103_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
return v___x_3104_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec(v_stx_2380_);
v___x_3105_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_dec(v_stx_2380_);
v___x_3107_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec(v_stx_2380_);
v___x_3109_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; size_t v_sz_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3111_ = lean_unsigned_to_nat(2u);
v___x_3112_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3111_);
v___x_3113_ = l_Lean_Syntax_getArgs(v___x_3112_);
lean_dec(v___x_3112_);
v_sz_3114_ = lean_array_size(v___x_3113_);
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3114_, v___x_3115_, v___x_3113_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_env_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3117_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3118_ = lean_st_ref_get(v_a_2386_);
v_env_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_env_3119_);
lean_dec(v___x_3118_);
v___x_3120_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3121_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3120_, v_env_3119_, v___x_3117_);
v___x_3122_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3123_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3121_, v___x_3122_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3121_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3154_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3154_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3154_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_fst_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3152_; 
v_fst_3128_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_a_3124_, 1);
lean_dec(v_unused_3153_);
v___x_3130_ = v_a_3124_;
v_isShared_3131_ = v_isSharedCheck_3152_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_fst_3128_);
lean_dec(v_a_3124_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3152_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
if (lean_obj_tag(v_fst_3128_) == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_del_object(v___x_3126_);
v___x_3132_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3133_ = l_Lean_MessageData_ofName(v___x_3117_);
lean_inc_ref(v___x_3133_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 7);
lean_ctor_set(v___x_3130_, 1, v___x_3133_);
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3136_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3139_ = l_Lean_indentD(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3137_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v___x_3133_);
v___x_3144_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3145_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3146_;
}
}
else
{
lean_object* v_val_3148_; lean_object* v___x_3150_; 
lean_del_object(v___x_3130_);
lean_dec(v___x_3117_);
lean_dec(v_stx_2380_);
v_val_3148_ = lean_ctor_get(v_fst_3128_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v_fst_3128_, 1);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v_val_3148_);
v___x_3150_ = v___x_3126_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_val_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v___x_3117_);
lean_dec(v_stx_2380_);
v_a_3155_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3123_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3123_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_val_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3297_; 
v_val_3163_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3165_ = v___x_3116_;
v_isShared_3166_ = v_isSharedCheck_3297_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_val_3163_);
lean_dec(v___x_3116_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3297_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v_finSeq_x3f_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3167_ = lean_unsigned_to_nat(1u);
v___x_3168_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3167_);
v___x_3192_ = lean_unsigned_to_nat(3u);
v___x_3193_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3192_);
v___x_3194_ = l_Lean_Syntax_isNone(v___x_3193_);
if (v___x_3194_ == 0)
{
uint8_t v___x_3195_; 
lean_inc(v___x_3193_);
v___x_3195_ = l_Lean_Syntax_matchesNull(v___x_3193_, v___x_3167_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_env_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_dec(v___x_3193_);
lean_dec(v___x_3168_);
lean_del_object(v___x_3165_);
lean_dec(v_val_3163_);
lean_inc_n(v_stx_2380_, 2);
v___x_3196_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3197_ = lean_st_ref_get(v_a_2386_);
v_env_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3198_);
lean_dec(v___x_3197_);
v___x_3199_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3200_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3199_, v_env_3198_, v___x_3196_);
v___x_3201_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3202_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3200_, v___x_3201_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3200_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3233_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3233_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3233_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v_fst_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3231_; 
v_fst_3207_ = lean_ctor_get(v_a_3203_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_a_3203_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v_a_3203_, 1);
lean_dec(v_unused_3232_);
v___x_3209_ = v_a_3203_;
v_isShared_3210_ = v_isSharedCheck_3231_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_fst_3207_);
lean_dec(v_a_3203_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3231_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
if (lean_obj_tag(v_fst_3207_) == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
lean_del_object(v___x_3205_);
v___x_3211_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3212_ = l_Lean_MessageData_ofName(v___x_3196_);
lean_inc_ref(v___x_3212_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 7);
lean_ctor_set(v___x_3209_, 1, v___x_3212_);
lean_ctor_set(v___x_3209_, 0, v___x_3211_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3215_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3218_ = l_Lean_indentD(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3216_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3212_);
v___x_3223_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3224_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3225_;
}
}
else
{
lean_object* v_val_3227_; lean_object* v___x_3229_; 
lean_del_object(v___x_3209_);
lean_dec(v___x_3196_);
lean_dec(v_stx_2380_);
v_val_3227_ = lean_ctor_get(v_fst_3207_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v_fst_3207_, 1);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v_val_3227_);
v___x_3229_ = v___x_3205_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_val_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v___x_3196_);
lean_dec(v_stx_2380_);
v_a_3234_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3202_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3202_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = l_Lean_Syntax_getArg(v___x_3193_, v___x_3242_);
lean_dec(v___x_3193_);
v___x_3244_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3243_);
v___x_3245_ = l_Lean_Syntax_isOfKind(v___x_3243_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_env_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v___x_3243_);
lean_dec(v___x_3168_);
lean_del_object(v___x_3165_);
lean_dec(v_val_3163_);
lean_inc_n(v_stx_2380_, 2);
v___x_3246_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3247_ = lean_st_ref_get(v_a_2386_);
v_env_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_env_3248_);
lean_dec(v___x_3247_);
v___x_3249_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3250_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3249_, v_env_3248_, v___x_3246_);
v___x_3251_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3252_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3250_, v___x_3251_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3250_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3283_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3283_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3283_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_fst_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3281_; 
v_fst_3257_ = lean_ctor_get(v_a_3253_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_a_3253_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_a_3253_, 1);
lean_dec(v_unused_3282_);
v___x_3259_ = v_a_3253_;
v_isShared_3260_ = v_isSharedCheck_3281_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_fst_3257_);
lean_dec(v_a_3253_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3281_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
if (lean_obj_tag(v_fst_3257_) == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_del_object(v___x_3255_);
v___x_3261_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3262_ = l_Lean_MessageData_ofName(v___x_3246_);
lean_inc_ref(v___x_3262_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 7);
lean_ctor_set(v___x_3259_, 1, v___x_3262_);
lean_ctor_set(v___x_3259_, 0, v___x_3261_);
v___x_3264_ = v___x_3259_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3265_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3268_ = l_Lean_indentD(v___x_3267_);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3266_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v___x_3262_);
v___x_3273_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3274_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3275_;
}
}
else
{
lean_object* v_val_3277_; lean_object* v___x_3279_; 
lean_del_object(v___x_3259_);
lean_dec(v___x_3246_);
lean_dec(v_stx_2380_);
v_val_3277_ = lean_ctor_get(v_fst_3257_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v_fst_3257_, 1);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v_val_3277_);
v___x_3279_ = v___x_3255_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_val_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v___x_3246_);
lean_dec(v_stx_2380_);
v_a_3284_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3252_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3252_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3294_; 
lean_dec(v_stx_2380_);
v___x_3292_ = l_Lean_Syntax_getArg(v___x_3243_, v___x_3167_);
lean_dec(v___x_3243_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3292_);
v___x_3294_ = v___x_3165_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
v_finSeq_x3f_3170_ = v___x_3294_;
v___y_3171_ = v_a_2381_;
v___y_3172_ = v_a_2382_;
v___y_3173_ = v_a_2383_;
v___y_3174_ = v_a_2384_;
v___y_3175_ = v_a_2385_;
v___y_3176_ = v_a_2386_;
goto v___jp_3169_;
}
}
}
}
else
{
lean_object* v___x_3296_; 
lean_dec(v___x_3193_);
lean_del_object(v___x_3165_);
lean_dec(v_stx_2380_);
v___x_3296_ = lean_box(0);
v_finSeq_x3f_3170_ = v___x_3296_;
v___y_3171_ = v_a_2381_;
v___y_3172_ = v_a_2382_;
v___y_3173_ = v_a_2383_;
v___y_3174_ = v_a_2384_;
v___y_3175_ = v_a_2385_;
v___y_3176_ = v_a_2386_;
goto v___jp_3169_;
}
v___jp_3169_:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3168_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; size_t v_sz_3179_; lean_object* v___x_3180_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v_sz_3179_ = lean_array_size(v_val_3163_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3163_, v_sz_3179_, v___x_3115_, v_a_3178_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v_val_3163_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3182_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3191_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3191_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3181_, v_a_3183_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
else
{
lean_dec(v_a_3181_);
return v___x_3182_;
}
}
else
{
lean_dec(v_finSeq_x3f_3170_);
return v___x_3180_;
}
}
else
{
lean_dec(v_finSeq_x3f_3170_);
lean_dec(v_val_3163_);
return v___x_3177_;
}
}
}
}
}
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_unsigned_to_nat(1u);
v___x_3422_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3299_);
v___x_3423_ = l_Lean_Syntax_isNone(v___x_3422_);
if (v___x_3423_ == 0)
{
uint8_t v___x_3424_; 
lean_inc(v___x_3422_);
v___x_3424_ = l_Lean_Syntax_matchesNull(v___x_3422_, v___x_3299_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_env_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v___x_3422_);
lean_inc_n(v_stx_2380_, 2);
v___x_3425_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3426_ = lean_st_ref_get(v_a_2386_);
v_env_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc_ref(v_env_3427_);
lean_dec(v___x_3426_);
v___x_3428_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3429_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3428_, v_env_3427_, v___x_3425_);
v___x_3430_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3431_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3429_, v___x_3430_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3429_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3462_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3462_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3462_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3460_; 
v_fst_3436_ = lean_ctor_get(v_a_3432_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v_a_3432_, 1);
lean_dec(v_unused_3461_);
v___x_3438_ = v_a_3432_;
v_isShared_3439_ = v_isSharedCheck_3460_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_fst_3436_);
lean_dec(v_a_3432_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3460_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_fst_3436_) == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
lean_del_object(v___x_3434_);
v___x_3440_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3441_ = l_Lean_MessageData_ofName(v___x_3425_);
lean_inc_ref(v___x_3441_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 7);
lean_ctor_set(v___x_3438_, 1, v___x_3441_);
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3444_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3447_ = l_Lean_indentD(v___x_3446_);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3445_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v___x_3441_);
v___x_3452_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3453_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3454_;
}
}
else
{
lean_object* v_val_3456_; lean_object* v___x_3458_; 
lean_del_object(v___x_3438_);
lean_dec(v___x_3425_);
lean_dec(v_stx_2380_);
v_val_3456_ = lean_ctor_get(v_fst_3436_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v_fst_3436_, 1);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_val_3456_);
v___x_3458_ = v___x_3434_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_val_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v___x_3425_);
lean_dec(v_stx_2380_);
v_a_3463_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3431_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3431_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = l_Lean_Syntax_getArg(v___x_3422_, v___x_3298_);
lean_dec(v___x_3422_);
v___x_3472_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3473_ = l_Lean_Syntax_isOfKind(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v_env_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3474_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3475_ = lean_st_ref_get(v_a_2386_);
v_env_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc_ref(v_env_3476_);
lean_dec(v___x_3475_);
v___x_3477_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3478_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3477_, v_env_3476_, v___x_3474_);
v___x_3479_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3480_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3478_, v___x_3479_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3478_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3511_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_fst_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3509_; 
v_fst_3485_ = lean_ctor_get(v_a_3481_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3481_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v_a_3481_, 1);
lean_dec(v_unused_3510_);
v___x_3487_ = v_a_3481_;
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_fst_3485_);
lean_dec(v_a_3481_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3509_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
if (lean_obj_tag(v_fst_3485_) == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_del_object(v___x_3483_);
v___x_3489_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3490_ = l_Lean_MessageData_ofName(v___x_3474_);
lean_inc_ref(v___x_3490_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set_tag(v___x_3487_, 7);
lean_ctor_set(v___x_3487_, 1, v___x_3490_);
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3492_ = v___x_3487_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3496_ = l_Lean_indentD(v___x_3495_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3490_);
v___x_3501_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3502_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3503_;
}
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3507_; 
lean_del_object(v___x_3487_);
lean_dec(v___x_3474_);
lean_dec(v_stx_2380_);
v_val_3505_ = lean_ctor_get(v_fst_3485_, 0);
lean_inc(v_val_3505_);
lean_dec_ref_known(v_fst_3485_, 1);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v_val_3505_);
v___x_3507_ = v___x_3483_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_val_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v___x_3474_);
lean_dec(v_stx_2380_);
v_a_3512_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3480_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3480_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
v___y_3317_ = v_a_2381_;
v___y_3318_ = v_a_2382_;
v___y_3319_ = v_a_2383_;
v___y_3320_ = v_a_2384_;
v___y_3321_ = v_a_2385_;
v___y_3322_ = v_a_2386_;
goto v___jp_3316_;
}
}
}
else
{
lean_dec(v___x_3422_);
v___y_3317_ = v_a_2381_;
v___y_3318_ = v_a_2382_;
v___y_3319_ = v_a_2383_;
v___y_3320_ = v_a_2384_;
v___y_3321_ = v_a_2385_;
v___y_3322_ = v_a_2386_;
goto v___jp_3316_;
}
v___jp_3300_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_unsigned_to_nat(3u);
v___x_3308_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3307_);
lean_dec(v_stx_2380_);
v___x_3309_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3308_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; uint8_t v_breaks_3311_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v_breaks_3311_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*2);
if (v_breaks_3311_ == 0)
{
uint8_t v_returnsEarly_3312_; lean_object* v_reassigns_3313_; 
v_returnsEarly_3312_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*2 + 2);
v_reassigns_3313_ = lean_ctor_get(v_a_3310_, 1);
lean_inc(v_reassigns_3313_);
lean_dec(v_a_3310_);
v___y_2714_ = v_reassigns_3313_;
v___y_2715_ = v_returnsEarly_3312_;
v___y_2716_ = v___x_3298_;
v___y_2717_ = v___x_2721_;
goto v___jp_2713_;
}
else
{
uint8_t v_returnsEarly_3314_; lean_object* v_reassigns_3315_; 
v_returnsEarly_3314_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*2 + 2);
v_reassigns_3315_ = lean_ctor_get(v_a_3310_, 1);
lean_inc(v_reassigns_3315_);
lean_dec(v_a_3310_);
v___y_2714_ = v_reassigns_3315_;
v___y_2715_ = v_returnsEarly_3314_;
v___y_2716_ = v___x_3299_;
v___y_2717_ = v___x_2712_;
goto v___jp_2713_;
}
}
else
{
return v___x_3309_;
}
}
v___jp_3316_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_unsigned_to_nat(2u);
v___x_3324_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3323_);
v___x_3325_ = l_Lean_Syntax_isNone(v___x_3324_);
if (v___x_3325_ == 0)
{
uint8_t v___x_3326_; 
lean_inc(v___x_3324_);
v___x_3326_ = l_Lean_Syntax_matchesNull(v___x_3324_, v___x_3299_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_env_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec(v___x_3324_);
lean_inc_n(v_stx_2380_, 2);
v___x_3327_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3328_ = lean_st_ref_get(v___y_3322_);
v_env_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc_ref(v_env_3329_);
lean_dec(v___x_3328_);
v___x_3330_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3331_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3330_, v_env_3329_, v___x_3327_);
v___x_3332_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3333_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3331_, v___x_3332_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___x_3331_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3364_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3364_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3364_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_fst_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3362_; 
v_fst_3338_ = lean_ctor_get(v_a_3334_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v_a_3334_, 1);
lean_dec(v_unused_3363_);
v___x_3340_ = v_a_3334_;
v_isShared_3341_ = v_isSharedCheck_3362_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_fst_3338_);
lean_dec(v_a_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3362_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_fst_3338_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_del_object(v___x_3336_);
v___x_3342_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3343_ = l_Lean_MessageData_ofName(v___x_3327_);
lean_inc_ref(v___x_3343_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 7);
lean_ctor_set(v___x_3340_, 1, v___x_3343_);
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3346_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3349_ = l_Lean_indentD(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v___x_3343_);
v___x_3354_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3355_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3356_;
}
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3360_; 
lean_del_object(v___x_3340_);
lean_dec(v___x_3327_);
lean_dec(v_stx_2380_);
v_val_3358_ = lean_ctor_get(v_fst_3338_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v_fst_3338_, 1);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_val_3358_);
v___x_3360_ = v___x_3336_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_val_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v___x_3327_);
lean_dec(v_stx_2380_);
v_a_3365_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3333_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3333_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3373_ = l_Lean_Syntax_getArg(v___x_3324_, v___x_3298_);
lean_dec(v___x_3324_);
v___x_3374_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3375_ = l_Lean_Syntax_isOfKind(v___x_3373_, v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v_env_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3376_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3377_ = lean_st_ref_get(v___y_3322_);
v_env_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc_ref(v_env_3378_);
lean_dec(v___x_3377_);
v___x_3379_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3380_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3379_, v_env_3378_, v___x_3376_);
v___x_3381_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3382_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3380_, v___x_3381_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___x_3380_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3413_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3413_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3413_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_fst_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3411_; 
v_fst_3387_ = lean_ctor_get(v_a_3383_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v_a_3383_, 1);
lean_dec(v_unused_3412_);
v___x_3389_ = v_a_3383_;
v_isShared_3390_ = v_isSharedCheck_3411_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_fst_3387_);
lean_dec(v_a_3383_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3411_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
if (lean_obj_tag(v_fst_3387_) == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_del_object(v___x_3385_);
v___x_3391_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3392_ = l_Lean_MessageData_ofName(v___x_3376_);
lean_inc_ref(v___x_3392_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 7);
lean_ctor_set(v___x_3389_, 1, v___x_3392_);
lean_ctor_set(v___x_3389_, 0, v___x_3391_);
v___x_3394_ = v___x_3389_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3395_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3398_ = l_Lean_indentD(v___x_3397_);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3396_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3392_);
v___x_3403_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3404_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3405_;
}
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3409_; 
lean_del_object(v___x_3389_);
lean_dec(v___x_3376_);
lean_dec(v_stx_2380_);
v_val_3407_ = lean_ctor_get(v_fst_3387_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v_fst_3387_, 1);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v_val_3407_);
v___x_3409_ = v___x_3385_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_val_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v___x_3376_);
lean_dec(v_stx_2380_);
v_a_3414_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3382_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3382_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
v___y_3301_ = v___y_3317_;
v___y_3302_ = v___y_3318_;
v___y_3303_ = v___y_3319_;
v___y_3304_ = v___y_3320_;
v___y_3305_ = v___y_3321_;
v___y_3306_ = v___y_3322_;
goto v___jp_3300_;
}
}
}
else
{
lean_dec(v___x_3324_);
v___y_3301_ = v___y_3317_;
v___y_3302_ = v___y_3318_;
v___y_3303_ = v___y_3319_;
v___y_3304_ = v___y_3320_;
v___y_3305_ = v___y_3321_;
v___y_3306_ = v___y_3322_;
goto v___jp_3300_;
}
}
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3657_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = lean_unsigned_to_nat(1u);
v___x_3806_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3521_);
v___x_3807_ = l_Lean_Syntax_getArgs(v___x_3806_);
lean_dec(v___x_3806_);
v___x_3808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3809_ = lean_array_get_size(v___x_3807_);
v___x_3810_ = lean_nat_dec_lt(v___x_3520_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_dec_ref(v___x_3807_);
v___y_3657_ = v___x_3808_;
goto v___jp_3656_;
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; lean_object* v___x_3815_; lean_object* v_snd_3816_; 
v___x_3811_ = lean_box(v___x_3810_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
lean_ctor_set(v___x_3812_, 1, v___x_3808_);
v___x_3813_ = ((size_t)0ULL);
v___x_3814_ = lean_usize_of_nat(v___x_3809_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2712_, v___x_2710_, v___x_3807_, v___x_3813_, v___x_3814_, v___x_3812_);
lean_dec_ref(v___x_3807_);
v_snd_3816_ = lean_ctor_get(v___x_3815_, 1);
lean_inc(v_snd_3816_);
lean_dec_ref(v___x_3815_);
v___y_3657_ = v_snd_3816_;
goto v___jp_3656_;
}
v___jp_3522_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_unsigned_to_nat(5u);
v___x_3530_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3529_);
lean_dec(v_stx_2380_);
v___x_3531_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3530_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3549_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3549_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3549_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
uint8_t v_returnsEarly_3536_; lean_object* v_reassigns_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3547_; 
v_returnsEarly_3536_ = lean_ctor_get_uint8(v_a_3532_, sizeof(void*)*2 + 2);
v_reassigns_3537_ = lean_ctor_get(v_a_3532_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_a_3532_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v_a_3532_, 0);
lean_dec(v_unused_3548_);
v___x_3539_ = v_a_3532_;
v_isShared_3540_ = v_isSharedCheck_3547_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_reassigns_3537_);
lean_dec(v_a_3532_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3547_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3521_);
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_reassigns_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3546_, sizeof(void*)*2 + 2, v_returnsEarly_3536_);
v___x_3542_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3544_; 
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*2, v___x_2710_);
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*2 + 1, v___x_2710_);
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*2 + 3, v___x_2710_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3542_);
v___x_3544_ = v___x_3534_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
else
{
return v___x_3531_;
}
}
v___jp_3550_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3557_ = lean_unsigned_to_nat(3u);
v___x_3558_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3557_);
v___x_3559_ = l_Lean_Syntax_isNone(v___x_3558_);
if (v___x_3559_ == 0)
{
uint8_t v___x_3560_; 
lean_inc(v___x_3558_);
v___x_3560_ = l_Lean_Syntax_matchesNull(v___x_3558_, v___x_3521_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v_env_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec(v___x_3558_);
lean_inc_n(v_stx_2380_, 2);
v___x_3561_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3562_ = lean_st_ref_get(v___y_3556_);
v_env_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc_ref(v_env_3563_);
lean_dec(v___x_3562_);
v___x_3564_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3565_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3564_, v_env_3563_, v___x_3561_);
v___x_3566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3567_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3565_, v___x_3566_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___x_3565_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3598_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3598_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_fst_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3596_; 
v_fst_3572_ = lean_ctor_get(v_a_3568_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_a_3568_, 1);
lean_dec(v_unused_3597_);
v___x_3574_ = v_a_3568_;
v_isShared_3575_ = v_isSharedCheck_3596_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_fst_3572_);
lean_dec(v_a_3568_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3596_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (lean_obj_tag(v_fst_3572_) == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_del_object(v___x_3570_);
v___x_3576_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3577_ = l_Lean_MessageData_ofName(v___x_3561_);
lean_inc_ref(v___x_3577_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 7);
lean_ctor_set(v___x_3574_, 1, v___x_3577_);
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3580_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3583_ = l_Lean_indentD(v___x_3582_);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3581_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v___x_3577_);
v___x_3588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3589_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3590_;
}
}
else
{
lean_object* v_val_3592_; lean_object* v___x_3594_; 
lean_del_object(v___x_3574_);
lean_dec(v___x_3561_);
lean_dec(v_stx_2380_);
v_val_3592_ = lean_ctor_get(v_fst_3572_, 0);
lean_inc(v_val_3592_);
lean_dec_ref_known(v_fst_3572_, 1);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_val_3592_);
v___x_3594_ = v___x_3570_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_val_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v___x_3561_);
lean_dec(v_stx_2380_);
v_a_3599_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3567_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3567_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3607_ = l_Lean_Syntax_getArg(v___x_3558_, v___x_3520_);
lean_dec(v___x_3558_);
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3609_ = l_Lean_Syntax_isOfKind(v___x_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_env_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3610_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3611_ = lean_st_ref_get(v___y_3556_);
v_env_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc_ref(v_env_3612_);
lean_dec(v___x_3611_);
v___x_3613_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3614_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3613_, v_env_3612_, v___x_3610_);
v___x_3615_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3616_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3614_, v___x_3615_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___x_3614_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3647_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3647_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3647_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v_fst_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3645_; 
v_fst_3621_ = lean_ctor_get(v_a_3617_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_a_3617_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v_a_3617_, 1);
lean_dec(v_unused_3646_);
v___x_3623_ = v_a_3617_;
v_isShared_3624_ = v_isSharedCheck_3645_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_fst_3621_);
lean_dec(v_a_3617_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3645_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
if (lean_obj_tag(v_fst_3621_) == 0)
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
lean_del_object(v___x_3619_);
v___x_3625_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3626_ = l_Lean_MessageData_ofName(v___x_3610_);
lean_inc_ref(v___x_3626_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set_tag(v___x_3623_, 7);
lean_ctor_set(v___x_3623_, 1, v___x_3626_);
lean_ctor_set(v___x_3623_, 0, v___x_3625_);
v___x_3628_ = v___x_3623_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3629_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3632_ = l_Lean_indentD(v___x_3631_);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3630_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
lean_ctor_set(v___x_3636_, 1, v___x_3626_);
v___x_3637_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3638_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3639_;
}
}
else
{
lean_object* v_val_3641_; lean_object* v___x_3643_; 
lean_del_object(v___x_3623_);
lean_dec(v___x_3610_);
lean_dec(v_stx_2380_);
v_val_3641_ = lean_ctor_get(v_fst_3621_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v_fst_3621_, 1);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v_val_3641_);
v___x_3643_ = v___x_3619_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_val_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v___x_3610_);
lean_dec(v_stx_2380_);
v_a_3648_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3616_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3616_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
v___y_3523_ = v___y_3551_;
v___y_3524_ = v___y_3552_;
v___y_3525_ = v___y_3553_;
v___y_3526_ = v___y_3554_;
v___y_3527_ = v___y_3555_;
v___y_3528_ = v___y_3556_;
goto v___jp_3522_;
}
}
}
else
{
lean_dec(v___x_3558_);
v___y_3523_ = v___y_3551_;
v___y_3524_ = v___y_3552_;
v___y_3525_ = v___y_3553_;
v___y_3526_ = v___y_3554_;
v___y_3527_ = v___y_3555_;
v___y_3528_ = v___y_3556_;
goto v___jp_3522_;
}
}
v___jp_3656_:
{
size_t v_sz_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v_sz_3658_ = lean_array_size(v___y_3657_);
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3658_, v___x_3659_, v___y_3657_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_env_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3661_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3662_ = lean_st_ref_get(v_a_2386_);
v_env_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc_ref(v_env_3663_);
lean_dec(v___x_3662_);
v___x_3664_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3665_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3664_, v_env_3663_, v___x_3661_);
v___x_3666_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3667_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3665_, v___x_3666_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3665_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3698_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3698_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3698_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_fst_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3696_; 
v_fst_3672_ = lean_ctor_get(v_a_3668_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_a_3668_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v_a_3668_, 1);
lean_dec(v_unused_3697_);
v___x_3674_ = v_a_3668_;
v_isShared_3675_ = v_isSharedCheck_3696_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_fst_3672_);
lean_dec(v_a_3668_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3696_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
if (lean_obj_tag(v_fst_3672_) == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
lean_del_object(v___x_3670_);
v___x_3676_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3677_ = l_Lean_MessageData_ofName(v___x_3661_);
lean_inc_ref(v___x_3677_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 7);
lean_ctor_set(v___x_3674_, 1, v___x_3677_);
lean_ctor_set(v___x_3674_, 0, v___x_3676_);
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3680_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3683_ = l_Lean_indentD(v___x_3682_);
v___x_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3681_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v___x_3677_);
v___x_3688_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3689_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3690_;
}
}
else
{
lean_object* v_val_3692_; lean_object* v___x_3694_; 
lean_del_object(v___x_3674_);
lean_dec(v___x_3661_);
lean_dec(v_stx_2380_);
v_val_3692_ = lean_ctor_get(v_fst_3672_, 0);
lean_inc(v_val_3692_);
lean_dec_ref_known(v_fst_3672_, 1);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_val_3692_);
v___x_3694_ = v___x_3670_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_val_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v___x_3661_);
lean_dec(v_stx_2380_);
v_a_3699_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3667_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3667_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
lean_dec_ref_known(v___x_3660_, 1);
v___x_3707_ = lean_unsigned_to_nat(2u);
v___x_3708_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3707_);
v___x_3709_ = l_Lean_Syntax_isNone(v___x_3708_);
if (v___x_3709_ == 0)
{
uint8_t v___x_3710_; 
lean_inc(v___x_3708_);
v___x_3710_ = l_Lean_Syntax_matchesNull(v___x_3708_, v___x_3521_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v_env_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec(v___x_3708_);
lean_inc_n(v_stx_2380_, 2);
v___x_3711_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3712_ = lean_st_ref_get(v_a_2386_);
v_env_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc_ref(v_env_3713_);
lean_dec(v___x_3712_);
v___x_3714_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3715_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3714_, v_env_3713_, v___x_3711_);
v___x_3716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3717_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3715_, v___x_3716_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3715_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3748_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3748_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3748_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_fst_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3746_; 
v_fst_3722_ = lean_ctor_get(v_a_3718_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_a_3718_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v_a_3718_, 1);
lean_dec(v_unused_3747_);
v___x_3724_ = v_a_3718_;
v_isShared_3725_ = v_isSharedCheck_3746_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_fst_3722_);
lean_dec(v_a_3718_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3746_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
if (lean_obj_tag(v_fst_3722_) == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_del_object(v___x_3720_);
v___x_3726_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3727_ = l_Lean_MessageData_ofName(v___x_3711_);
lean_inc_ref(v___x_3727_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set_tag(v___x_3724_, 7);
lean_ctor_set(v___x_3724_, 1, v___x_3727_);
lean_ctor_set(v___x_3724_, 0, v___x_3726_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3730_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3733_ = l_Lean_indentD(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3731_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3727_);
v___x_3738_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3739_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3740_;
}
}
else
{
lean_object* v_val_3742_; lean_object* v___x_3744_; 
lean_del_object(v___x_3724_);
lean_dec(v___x_3711_);
lean_dec(v_stx_2380_);
v_val_3742_ = lean_ctor_get(v_fst_3722_, 0);
lean_inc(v_val_3742_);
lean_dec_ref_known(v_fst_3722_, 1);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_val_3742_);
v___x_3744_ = v___x_3720_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_val_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v___x_3711_);
lean_dec(v_stx_2380_);
v_a_3749_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3717_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3717_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3757_ = l_Lean_Syntax_getArg(v___x_3708_, v___x_3520_);
lean_dec(v___x_3708_);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3759_ = l_Lean_Syntax_isOfKind(v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v_env_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3760_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3761_ = lean_st_ref_get(v_a_2386_);
v_env_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc_ref(v_env_3762_);
lean_dec(v___x_3761_);
v___x_3763_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3764_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3763_, v_env_3762_, v___x_3760_);
v___x_3765_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3766_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3764_, v___x_3765_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3764_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3797_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3797_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3797_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_fst_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3795_; 
v_fst_3771_ = lean_ctor_get(v_a_3767_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v_a_3767_, 1);
lean_dec(v_unused_3796_);
v___x_3773_ = v_a_3767_;
v_isShared_3774_ = v_isSharedCheck_3795_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_fst_3771_);
lean_dec(v_a_3767_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3795_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
if (lean_obj_tag(v_fst_3771_) == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
lean_del_object(v___x_3769_);
v___x_3775_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3776_ = l_Lean_MessageData_ofName(v___x_3760_);
lean_inc_ref(v___x_3776_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set_tag(v___x_3773_, 7);
lean_ctor_set(v___x_3773_, 1, v___x_3776_);
lean_ctor_set(v___x_3773_, 0, v___x_3775_);
v___x_3778_ = v___x_3773_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3779_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3782_ = l_Lean_indentD(v___x_3781_);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3780_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v___x_3776_);
v___x_3787_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3788_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3789_;
}
}
else
{
lean_object* v_val_3791_; lean_object* v___x_3793_; 
lean_del_object(v___x_3773_);
lean_dec(v___x_3760_);
lean_dec(v_stx_2380_);
v_val_3791_ = lean_ctor_get(v_fst_3771_, 0);
lean_inc(v_val_3791_);
lean_dec_ref_known(v_fst_3771_, 1);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_val_3791_);
v___x_3793_ = v___x_3769_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_val_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v___x_3760_);
lean_dec(v_stx_2380_);
v_a_3798_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3766_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3766_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
v___y_3551_ = v_a_2381_;
v___y_3552_ = v_a_2382_;
v___y_3553_ = v_a_2383_;
v___y_3554_ = v_a_2384_;
v___y_3555_ = v_a_2385_;
v___y_3556_ = v_a_2386_;
goto v___jp_3550_;
}
}
}
else
{
lean_dec(v___x_3708_);
v___y_3551_ = v_a_2381_;
v___y_3552_ = v_a_2382_;
v___y_3553_ = v_a_2383_;
v___y_3554_ = v_a_2384_;
v___y_3555_ = v_a_2385_;
v___y_3556_ = v_a_2386_;
goto v___jp_3550_;
}
}
}
}
v___jp_2713_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2718_, 0, v___y_2716_);
lean_ctor_set(v___x_2718_, 1, v___y_2714_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*2, v___x_2712_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*2 + 1, v___x_2712_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*2 + 2, v___y_2715_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*2 + 3, v___y_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = lean_unsigned_to_nat(3u);
v___x_3819_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3818_);
lean_dec(v_stx_2380_);
v___x_3820_ = l_Lean_NameSet_empty;
v___x_3821_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3821_, 0, v___x_3817_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2, v___x_2708_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2 + 1, v___x_2708_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2 + 2, v___x_2708_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2 + 3, v___x_2708_);
v___x_3822_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3819_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3831_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3821_, v_a_3823_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
else
{
lean_dec_ref_known(v___x_3821_, 2);
return v___x_3822_;
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; size_t v_sz_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v___x_3832_ = lean_unsigned_to_nat(4u);
v___x_3833_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3832_);
v___x_3834_ = l_Lean_Syntax_getArgs(v___x_3833_);
lean_dec(v___x_3833_);
v_sz_3835_ = lean_array_size(v___x_3834_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3835_, v___x_3836_, v___x_3834_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v_env_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_inc_n(v_stx_2380_, 2);
v___x_3838_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3839_ = lean_st_ref_get(v_a_2386_);
v_env_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref(v_env_3840_);
lean_dec(v___x_3839_);
v___x_3841_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3842_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3841_, v_env_3840_, v___x_3838_);
v___x_3843_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3844_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3842_, v___x_3843_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3842_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3875_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3875_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3875_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_fst_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3873_; 
v_fst_3849_ = lean_ctor_get(v_a_3845_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_a_3845_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; 
v_unused_3874_ = lean_ctor_get(v_a_3845_, 1);
lean_dec(v_unused_3874_);
v___x_3851_ = v_a_3845_;
v_isShared_3852_ = v_isSharedCheck_3873_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_fst_3849_);
lean_dec(v_a_3845_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3873_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
if (lean_obj_tag(v_fst_3849_) == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_del_object(v___x_3847_);
v___x_3853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3854_ = l_Lean_MessageData_ofName(v___x_3838_);
lean_inc_ref(v___x_3854_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 7);
lean_ctor_set(v___x_3851_, 1, v___x_3854_);
lean_ctor_set(v___x_3851_, 0, v___x_3853_);
v___x_3856_ = v___x_3851_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3857_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3860_ = l_Lean_indentD(v___x_3859_);
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3858_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___x_3854_);
v___x_3865_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3866_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3867_;
}
}
else
{
lean_object* v_val_3869_; lean_object* v___x_3871_; 
lean_del_object(v___x_3851_);
lean_dec(v___x_3838_);
lean_dec(v_stx_2380_);
v_val_3869_ = lean_ctor_get(v_fst_3849_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v_fst_3849_, 1);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_val_3869_);
v___x_3871_ = v___x_3847_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_val_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec(v___x_3838_);
lean_dec(v_stx_2380_);
v_a_3876_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3844_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3844_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_val_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3971_; 
v_val_3884_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3886_ = v___x_3837_;
v_isShared_3887_ = v_isSharedCheck_3971_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_val_3884_);
lean_dec(v___x_3837_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3971_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v_elseSeq_x3f_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3888_ = lean_unsigned_to_nat(3u);
v___x_3889_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3888_);
v___x_3914_ = lean_unsigned_to_nat(5u);
v___x_3915_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3914_);
v___x_3916_ = l_Lean_Syntax_isNone(v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; uint8_t v___x_3918_; 
v___x_3917_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3915_);
v___x_3918_ = l_Lean_Syntax_matchesNull(v___x_3915_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_env_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec(v___x_3915_);
lean_dec(v___x_3889_);
lean_del_object(v___x_3886_);
lean_dec(v_val_3884_);
lean_inc_n(v_stx_2380_, 2);
v___x_3919_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3920_ = lean_st_ref_get(v_a_2386_);
v_env_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_env_3921_);
lean_dec(v___x_3920_);
v___x_3922_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3923_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3922_, v_env_3921_, v___x_3919_);
v___x_3924_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3925_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3923_, v___x_3924_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3956_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3956_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3956_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v_fst_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3954_; 
v_fst_3930_ = lean_ctor_get(v_a_3926_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3926_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; 
v_unused_3955_ = lean_ctor_get(v_a_3926_, 1);
lean_dec(v_unused_3955_);
v___x_3932_ = v_a_3926_;
v_isShared_3933_ = v_isSharedCheck_3954_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_fst_3930_);
lean_dec(v_a_3926_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3954_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
if (lean_obj_tag(v_fst_3930_) == 0)
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
lean_del_object(v___x_3928_);
v___x_3934_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3935_ = l_Lean_MessageData_ofName(v___x_3919_);
lean_inc_ref(v___x_3935_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set_tag(v___x_3932_, 7);
lean_ctor_set(v___x_3932_, 1, v___x_3935_);
lean_ctor_set(v___x_3932_, 0, v___x_3934_);
v___x_3937_ = v___x_3932_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_3941_ = l_Lean_indentD(v___x_3940_);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3939_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v___x_3935_);
v___x_3946_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3947_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_3948_;
}
}
else
{
lean_object* v_val_3950_; lean_object* v___x_3952_; 
lean_del_object(v___x_3932_);
lean_dec(v___x_3919_);
lean_dec(v_stx_2380_);
v_val_3950_ = lean_ctor_get(v_fst_3930_, 0);
lean_inc(v_val_3950_);
lean_dec_ref_known(v_fst_3930_, 1);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v_val_3950_);
v___x_3952_ = v___x_3928_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_val_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v___x_3919_);
lean_dec(v_stx_2380_);
v_a_3957_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3925_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3925_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
lean_dec(v_stx_2380_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = l_Lean_Syntax_getArg(v___x_3915_, v___x_3965_);
lean_dec(v___x_3915_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3966_);
v___x_3968_ = v___x_3886_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
v_elseSeq_x3f_3891_ = v___x_3968_;
v___y_3892_ = v_a_2381_;
v___y_3893_ = v_a_2382_;
v___y_3894_ = v_a_2383_;
v___y_3895_ = v_a_2384_;
v___y_3896_ = v_a_2385_;
v___y_3897_ = v_a_2386_;
goto v___jp_3890_;
}
}
}
else
{
lean_object* v___x_3970_; 
lean_dec(v___x_3915_);
lean_del_object(v___x_3886_);
lean_dec(v_stx_2380_);
v___x_3970_ = lean_box(0);
v_elseSeq_x3f_3891_ = v___x_3970_;
v___y_3892_ = v_a_2381_;
v___y_3893_ = v_a_2382_;
v___y_3894_ = v_a_2383_;
v___y_3895_ = v_a_2384_;
v___y_3896_ = v_a_2385_;
v___y_3897_ = v_a_2386_;
goto v___jp_3890_;
}
v___jp_3890_:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; size_t v_sz_3901_; lean_object* v___x_3902_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
v___x_3900_ = l_Array_reverse___redArg(v_val_3884_);
v_sz_3901_ = lean_array_size(v___x_3900_);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3900_, v_sz_3901_, v___x_3836_, v_a_3899_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec_ref(v___x_3900_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3889_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3913_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3905_, v_a_3903_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3909_);
v___x_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
lean_dec(v_a_3903_);
return v___x_3904_;
}
}
else
{
lean_dec(v___x_3889_);
return v___x_3902_;
}
}
else
{
lean_dec(v___x_3889_);
lean_dec(v_val_3884_);
return v___x_3898_;
}
}
}
}
}
}
else
{
lean_object* v___x_3972_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___x_4036_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___x_4143_; uint8_t v___x_4144_; 
v___x_3972_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_unsigned_to_nat(1u);
v___x_4143_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4036_);
v___x_4144_ = l_Lean_Syntax_isNone(v___x_4143_);
if (v___x_4144_ == 0)
{
uint8_t v___x_4145_; 
lean_inc(v___x_4143_);
v___x_4145_ = l_Lean_Syntax_matchesNull(v___x_4143_, v___x_4036_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v_env_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v___x_4143_);
lean_inc_n(v_stx_2380_, 2);
v___x_4146_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4147_ = lean_st_ref_get(v_a_2386_);
v_env_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc_ref(v_env_4148_);
lean_dec(v___x_4147_);
v___x_4149_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4150_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4149_, v_env_4148_, v___x_4146_);
v___x_4151_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4152_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4150_, v___x_4151_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4150_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4183_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4183_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4183_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v_fst_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4181_; 
v_fst_4157_ = lean_ctor_get(v_a_4153_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_a_4153_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v_a_4153_, 1);
lean_dec(v_unused_4182_);
v___x_4159_ = v_a_4153_;
v_isShared_4160_ = v_isSharedCheck_4181_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_fst_4157_);
lean_dec(v_a_4153_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4181_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
if (lean_obj_tag(v_fst_4157_) == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
lean_del_object(v___x_4155_);
v___x_4161_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4162_ = l_Lean_MessageData_ofName(v___x_4146_);
lean_inc_ref(v___x_4162_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 7);
lean_ctor_set(v___x_4159_, 1, v___x_4162_);
lean_ctor_set(v___x_4159_, 0, v___x_4161_);
v___x_4164_ = v___x_4159_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4165_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4164_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4168_ = l_Lean_indentD(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4166_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v___x_4162_);
v___x_4173_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4174_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4175_;
}
}
else
{
lean_object* v_val_4177_; lean_object* v___x_4179_; 
lean_del_object(v___x_4159_);
lean_dec(v___x_4146_);
lean_dec(v_stx_2380_);
v_val_4177_ = lean_ctor_get(v_fst_4157_, 0);
lean_inc(v_val_4177_);
lean_dec_ref_known(v_fst_4157_, 1);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v_val_4177_);
v___x_4179_ = v___x_4155_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_val_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec(v___x_4146_);
lean_dec(v_stx_2380_);
v_a_4184_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4152_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4152_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v___x_4192_ = l_Lean_Syntax_getArg(v___x_4143_, v___x_3972_);
lean_dec(v___x_4143_);
v___x_4193_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4194_ = l_Lean_Syntax_isOfKind(v___x_4192_, v___x_4193_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v_env_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4195_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4196_ = lean_st_ref_get(v_a_2386_);
v_env_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc_ref(v_env_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4199_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4198_, v_env_4197_, v___x_4195_);
v___x_4200_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4201_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4199_, v___x_4200_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4199_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4232_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4232_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4232_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_fst_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4230_; 
v_fst_4206_ = lean_ctor_get(v_a_4202_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_a_4202_);
if (v_isSharedCheck_4230_ == 0)
{
lean_object* v_unused_4231_; 
v_unused_4231_ = lean_ctor_get(v_a_4202_, 1);
lean_dec(v_unused_4231_);
v___x_4208_ = v_a_4202_;
v_isShared_4209_ = v_isSharedCheck_4230_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_fst_4206_);
lean_dec(v_a_4202_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4230_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
if (lean_obj_tag(v_fst_4206_) == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
lean_del_object(v___x_4204_);
v___x_4210_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4211_ = l_Lean_MessageData_ofName(v___x_4195_);
lean_inc_ref(v___x_4211_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 7);
lean_ctor_set(v___x_4208_, 1, v___x_4211_);
lean_ctor_set(v___x_4208_, 0, v___x_4210_);
v___x_4213_ = v___x_4208_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4214_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4217_ = l_Lean_indentD(v___x_4216_);
v___x_4218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4215_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4218_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v___x_4221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v___x_4211_);
v___x_4222_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4221_);
lean_ctor_set(v___x_4223_, 1, v___x_4222_);
v___x_4224_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4223_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4224_;
}
}
else
{
lean_object* v_val_4226_; lean_object* v___x_4228_; 
lean_del_object(v___x_4208_);
lean_dec(v___x_4195_);
lean_dec(v_stx_2380_);
v_val_4226_ = lean_ctor_get(v_fst_4206_, 0);
lean_inc(v_val_4226_);
lean_dec_ref_known(v_fst_4206_, 1);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v_val_4226_);
v___x_4228_ = v___x_4204_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_val_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v___x_4195_);
lean_dec(v_stx_2380_);
v_a_4233_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4201_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4201_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
v___y_4038_ = v_a_2381_;
v___y_4039_ = v_a_2382_;
v___y_4040_ = v_a_2383_;
v___y_4041_ = v_a_2384_;
v___y_4042_ = v_a_2385_;
v___y_4043_ = v_a_2386_;
goto v___jp_4037_;
}
}
}
else
{
lean_dec(v___x_4143_);
v___y_4038_ = v_a_2381_;
v___y_4039_ = v_a_2382_;
v___y_4040_ = v_a_2383_;
v___y_4041_ = v_a_2384_;
v___y_4042_ = v_a_2385_;
v___y_4043_ = v_a_2386_;
goto v___jp_4037_;
}
v___jp_3973_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3980_ = lean_unsigned_to_nat(6u);
v___x_3981_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_3980_);
v___x_3982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3981_);
v___x_3983_ = l_Lean_Syntax_isOfKind(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_env_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec(v___x_3981_);
lean_inc_n(v_stx_2380_, 2);
v___x_3984_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_3985_ = lean_st_ref_get(v___y_3979_);
v_env_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc_ref(v_env_3986_);
lean_dec(v___x_3985_);
v___x_3987_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3988_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3987_, v_env_3986_, v___x_3984_);
v___x_3989_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3990_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_3988_, v___x_3989_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___x_3988_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4021_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4021_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4021_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_fst_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4019_; 
v_fst_3995_ = lean_ctor_get(v_a_3991_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_a_3991_);
if (v_isSharedCheck_4019_ == 0)
{
lean_object* v_unused_4020_; 
v_unused_4020_ = lean_ctor_get(v_a_3991_, 1);
lean_dec(v_unused_4020_);
v___x_3997_ = v_a_3991_;
v_isShared_3998_ = v_isSharedCheck_4019_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_fst_3995_);
lean_dec(v_a_3991_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4019_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
if (lean_obj_tag(v_fst_3995_) == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
lean_del_object(v___x_3993_);
v___x_3999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4000_ = l_Lean_MessageData_ofName(v___x_3984_);
lean_inc_ref(v___x_4000_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 7);
lean_ctor_set(v___x_3997_, 1, v___x_4000_);
lean_ctor_set(v___x_3997_, 0, v___x_3999_);
v___x_4002_ = v___x_3997_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4003_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4002_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4006_ = l_Lean_indentD(v___x_4005_);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4004_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v___x_4000_);
v___x_4011_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4010_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v___x_4013_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4012_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
return v___x_4013_;
}
}
else
{
lean_object* v_val_4015_; lean_object* v___x_4017_; 
lean_del_object(v___x_3997_);
lean_dec(v___x_3984_);
lean_dec(v_stx_2380_);
v_val_4015_ = lean_ctor_get(v_fst_3995_, 0);
lean_inc(v_val_4015_);
lean_dec_ref_known(v_fst_3995_, 1);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v_val_4015_);
v___x_4017_ = v___x_3993_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_val_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v___x_3984_);
lean_dec(v_stx_2380_);
v_a_4022_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3990_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3990_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; 
lean_dec(v_stx_2380_);
v___x_4030_ = l_Lean_Syntax_getArg(v___x_3981_, v___x_3972_);
lean_dec(v___x_3981_);
v___x_4031_ = l_Lean_Syntax_getArgs(v___x_4030_);
lean_dec(v___x_4030_);
v___x_4032_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4033_ = lean_array_size(v___x_4031_);
v___x_4034_ = ((size_t)0ULL);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2704_, v___x_4031_, v_sz_4033_, v___x_4034_, v___x_4032_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec_ref(v___x_4031_);
return v___x_4035_;
}
}
v___jp_4037_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = lean_unsigned_to_nat(2u);
v___x_4045_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4044_);
v___x_4046_ = l_Lean_Syntax_isNone(v___x_4045_);
if (v___x_4046_ == 0)
{
uint8_t v___x_4047_; 
lean_inc(v___x_4045_);
v___x_4047_ = l_Lean_Syntax_matchesNull(v___x_4045_, v___x_4036_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v_env_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec(v___x_4045_);
lean_inc_n(v_stx_2380_, 2);
v___x_4048_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4049_ = lean_st_ref_get(v___y_4043_);
v_env_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc_ref(v_env_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4052_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4051_, v_env_4050_, v___x_4048_);
v___x_4053_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4054_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4052_, v___x_4053_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___x_4052_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4085_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4085_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4085_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_fst_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4083_; 
v_fst_4059_ = lean_ctor_get(v_a_4055_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_a_4055_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v_a_4055_, 1);
lean_dec(v_unused_4084_);
v___x_4061_ = v_a_4055_;
v_isShared_4062_ = v_isSharedCheck_4083_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_fst_4059_);
lean_dec(v_a_4055_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4083_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
if (lean_obj_tag(v_fst_4059_) == 0)
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
lean_del_object(v___x_4057_);
v___x_4063_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4064_ = l_Lean_MessageData_ofName(v___x_4048_);
lean_inc_ref(v___x_4064_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set_tag(v___x_4061_, 7);
lean_ctor_set(v___x_4061_, 1, v___x_4064_);
lean_ctor_set(v___x_4061_, 0, v___x_4063_);
v___x_4066_ = v___x_4061_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4067_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4070_ = l_Lean_indentD(v___x_4069_);
v___x_4071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4068_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4064_);
v___x_4075_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4074_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4076_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
return v___x_4077_;
}
}
else
{
lean_object* v_val_4079_; lean_object* v___x_4081_; 
lean_del_object(v___x_4061_);
lean_dec(v___x_4048_);
lean_dec(v_stx_2380_);
v_val_4079_ = lean_ctor_get(v_fst_4059_, 0);
lean_inc(v_val_4079_);
lean_dec_ref_known(v_fst_4059_, 1);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v_val_4079_);
v___x_4081_ = v___x_4057_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_val_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v___x_4048_);
lean_dec(v_stx_2380_);
v_a_4086_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4054_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4054_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4094_ = l_Lean_Syntax_getArg(v___x_4045_, v___x_3972_);
lean_dec(v___x_4045_);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4096_ = l_Lean_Syntax_isOfKind(v___x_4094_, v___x_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v_env_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4097_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4098_ = lean_st_ref_get(v___y_4043_);
v_env_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc_ref(v_env_4099_);
lean_dec(v___x_4098_);
v___x_4100_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4101_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4100_, v_env_4099_, v___x_4097_);
v___x_4102_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4103_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4101_, v___x_4102_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___x_4101_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4134_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4134_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4134_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v_fst_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4132_; 
v_fst_4108_ = lean_ctor_get(v_a_4104_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_a_4104_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v_a_4104_, 1);
lean_dec(v_unused_4133_);
v___x_4110_ = v_a_4104_;
v_isShared_4111_ = v_isSharedCheck_4132_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_fst_4108_);
lean_dec(v_a_4104_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4132_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
if (lean_obj_tag(v_fst_4108_) == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_del_object(v___x_4106_);
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4113_ = l_Lean_MessageData_ofName(v___x_4097_);
lean_inc_ref(v___x_4113_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set_tag(v___x_4110_, 7);
lean_ctor_set(v___x_4110_, 1, v___x_4113_);
lean_ctor_set(v___x_4110_, 0, v___x_4112_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4116_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4119_ = l_Lean_indentD(v___x_4118_);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4117_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v___x_4113_);
v___x_4124_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4125_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
return v___x_4126_;
}
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4130_; 
lean_del_object(v___x_4110_);
lean_dec(v___x_4097_);
lean_dec(v_stx_2380_);
v_val_4128_ = lean_ctor_get(v_fst_4108_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v_fst_4108_, 1);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v_val_4128_);
v___x_4130_ = v___x_4106_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_val_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v___x_4097_);
lean_dec(v_stx_2380_);
v_a_4135_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4103_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4103_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
v___y_3974_ = v___y_4038_;
v___y_3975_ = v___y_4039_;
v___y_3976_ = v___y_4040_;
v___y_3977_ = v___y_4041_;
v___y_3978_ = v___y_4042_;
v___y_3979_ = v___y_4043_;
goto v___jp_3973_;
}
}
}
else
{
lean_dec(v___x_4045_);
v___y_3974_ = v___y_4038_;
v___y_3975_ = v___y_4039_;
v___y_3976_ = v___y_4040_;
v___y_3977_ = v___y_4041_;
v___y_3978_ = v___y_4042_;
v___y_3979_ = v___y_4043_;
goto v___jp_3973_;
}
}
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4241_);
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4242_);
v___x_4244_ = l_Lean_Syntax_isOfKind(v___x_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; uint8_t v___x_4246_; 
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4242_);
v___x_4246_ = l_Lean_Syntax_isOfKind(v___x_4242_, v___x_4245_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v_env_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec(v___x_4242_);
lean_inc_n(v_stx_2380_, 2);
v___x_4247_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4248_ = lean_st_ref_get(v_a_2386_);
v_env_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc_ref(v_env_4249_);
lean_dec(v___x_4248_);
v___x_4250_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4251_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4250_, v_env_4249_, v___x_4247_);
v___x_4252_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4253_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4251_, v___x_4252_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4251_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4284_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4284_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4284_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v_fst_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4282_; 
v_fst_4258_ = lean_ctor_get(v_a_4254_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_a_4254_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; 
v_unused_4283_ = lean_ctor_get(v_a_4254_, 1);
lean_dec(v_unused_4283_);
v___x_4260_ = v_a_4254_;
v_isShared_4261_ = v_isSharedCheck_4282_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_fst_4258_);
lean_dec(v_a_4254_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4282_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
if (lean_obj_tag(v_fst_4258_) == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4265_; 
lean_del_object(v___x_4256_);
v___x_4262_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4263_ = l_Lean_MessageData_ofName(v___x_4247_);
lean_inc_ref(v___x_4263_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 7);
lean_ctor_set(v___x_4260_, 1, v___x_4263_);
lean_ctor_set(v___x_4260_, 0, v___x_4262_);
v___x_4265_ = v___x_4260_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4262_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4266_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4269_ = l_Lean_indentD(v___x_4268_);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4267_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
lean_ctor_set(v___x_4273_, 1, v___x_4263_);
v___x_4274_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4273_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4275_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4276_;
}
}
else
{
lean_object* v_val_4278_; lean_object* v___x_4280_; 
lean_del_object(v___x_4260_);
lean_dec(v___x_4247_);
lean_dec(v_stx_2380_);
v_val_4278_ = lean_ctor_get(v_fst_4258_, 0);
lean_inc(v_val_4278_);
lean_dec_ref_known(v_fst_4258_, 1);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v_val_4278_);
v___x_4280_ = v___x_4256_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_val_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v___x_4247_);
lean_dec(v_stx_2380_);
v_a_4285_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4253_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4253_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_object* v___x_4293_; 
lean_dec(v_stx_2380_);
v___x_4293_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2620_, v___x_4242_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4293_;
}
}
else
{
lean_object* v___x_4294_; 
lean_dec(v_stx_2380_);
v___x_4294_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2620_, v___x_4242_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4294_;
}
}
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4295_ = lean_unsigned_to_nat(0u);
v___x_4296_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4295_);
v___x_4297_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4296_);
v___x_4298_ = l_Lean_Syntax_isOfKind(v___x_4296_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4299_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4296_);
v___x_4300_ = l_Lean_Syntax_isOfKind(v___x_4296_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v_env_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_dec(v___x_4296_);
lean_inc_n(v_stx_2380_, 2);
v___x_4301_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4302_ = lean_st_ref_get(v_a_2386_);
v_env_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc_ref(v_env_4303_);
lean_dec(v___x_4302_);
v___x_4304_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4305_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4304_, v_env_4303_, v___x_4301_);
v___x_4306_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4307_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4305_, v___x_4306_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4305_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4338_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4338_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4338_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v_fst_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4336_; 
v_fst_4312_ = lean_ctor_get(v_a_4308_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_a_4308_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v_a_4308_, 1);
lean_dec(v_unused_4337_);
v___x_4314_ = v_a_4308_;
v_isShared_4315_ = v_isSharedCheck_4336_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_fst_4312_);
lean_dec(v_a_4308_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4336_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
if (lean_obj_tag(v_fst_4312_) == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_del_object(v___x_4310_);
v___x_4316_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4317_ = l_Lean_MessageData_ofName(v___x_4301_);
lean_inc_ref(v___x_4317_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 7);
lean_ctor_set(v___x_4314_, 1, v___x_4317_);
lean_ctor_set(v___x_4314_, 0, v___x_4316_);
v___x_4319_ = v___x_4314_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4320_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4323_ = l_Lean_indentD(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4321_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4324_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
lean_ctor_set(v___x_4327_, 1, v___x_4317_);
v___x_4328_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4329_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4330_;
}
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; 
lean_del_object(v___x_4314_);
lean_dec(v___x_4301_);
lean_dec(v_stx_2380_);
v_val_4332_ = lean_ctor_get(v_fst_4312_, 0);
lean_inc(v_val_4332_);
lean_dec_ref_known(v_fst_4312_, 1);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v_val_4332_);
v___x_4334_ = v___x_4310_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_val_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v___x_4301_);
lean_dec(v_stx_2380_);
v_a_4339_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4307_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4307_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v___x_4347_; 
lean_dec(v_stx_2380_);
v___x_4347_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4296_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4296_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4349_ = lean_box(0);
v___x_4350_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4348_, v___x_4349_, v___x_4349_, v___x_4349_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4350_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
v_a_4351_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4347_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4347_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
else
{
lean_object* v___x_4359_; 
lean_dec(v_stx_2380_);
v___x_4359_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4296_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4296_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v___x_4361_ = lean_box(0);
v___x_4362_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4360_, v___x_4361_, v___x_4361_, v___x_4361_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4362_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
v_a_4363_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4359_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4359_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4371_);
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4372_);
v___x_4374_ = l_Lean_Syntax_isOfKind(v___x_4372_, v___x_4373_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_env_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_dec(v___x_4372_);
lean_inc_n(v_stx_2380_, 2);
v___x_4375_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4376_ = lean_st_ref_get(v_a_2386_);
v_env_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc_ref(v_env_4377_);
lean_dec(v___x_4376_);
v___x_4378_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4379_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4378_, v_env_4377_, v___x_4375_);
v___x_4380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4381_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4379_, v___x_4380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4379_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4412_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4412_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4412_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v_fst_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4410_; 
v_fst_4386_ = lean_ctor_get(v_a_4382_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_a_4382_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v_a_4382_, 1);
lean_dec(v_unused_4411_);
v___x_4388_ = v_a_4382_;
v_isShared_4389_ = v_isSharedCheck_4410_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_fst_4386_);
lean_dec(v_a_4382_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4410_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
if (lean_obj_tag(v_fst_4386_) == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
lean_del_object(v___x_4384_);
v___x_4390_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4391_ = l_Lean_MessageData_ofName(v___x_4375_);
lean_inc_ref(v___x_4391_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 7);
lean_ctor_set(v___x_4388_, 1, v___x_4391_);
lean_ctor_set(v___x_4388_, 0, v___x_4390_);
v___x_4393_ = v___x_4388_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4394_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4397_ = l_Lean_indentD(v___x_4396_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4395_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
lean_ctor_set(v___x_4401_, 1, v___x_4391_);
v___x_4402_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4401_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4403_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4404_;
}
}
else
{
lean_object* v_val_4406_; lean_object* v___x_4408_; 
lean_del_object(v___x_4388_);
lean_dec(v___x_4375_);
lean_dec(v_stx_2380_);
v_val_4406_ = lean_ctor_get(v_fst_4386_, 0);
lean_inc(v_val_4406_);
lean_dec_ref_known(v_fst_4386_, 1);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v_val_4406_);
v___x_4408_ = v___x_4384_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_val_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v___x_4375_);
lean_dec(v_stx_2380_);
v_a_4413_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4381_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4381_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v___x_4421_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4421_ = lean_unsigned_to_nat(1u);
v___x_4527_ = l_Lean_Syntax_getArg(v___x_4372_, v___x_4421_);
lean_dec(v___x_4372_);
v___x_4528_ = l_Lean_Syntax_isNone(v___x_4527_);
if (v___x_4528_ == 0)
{
uint8_t v___x_4529_; 
v___x_4529_ = l_Lean_Syntax_matchesNull(v___x_4527_, v___x_4421_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v_env_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4530_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4531_ = lean_st_ref_get(v_a_2386_);
v_env_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc_ref(v_env_4532_);
lean_dec(v___x_4531_);
v___x_4533_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4534_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4533_, v_env_4532_, v___x_4530_);
v___x_4535_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4536_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4534_, v___x_4535_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4534_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4567_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4567_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4567_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v_fst_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4565_; 
v_fst_4541_ = lean_ctor_get(v_a_4537_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v_a_4537_);
if (v_isSharedCheck_4565_ == 0)
{
lean_object* v_unused_4566_; 
v_unused_4566_ = lean_ctor_get(v_a_4537_, 1);
lean_dec(v_unused_4566_);
v___x_4543_ = v_a_4537_;
v_isShared_4544_ = v_isSharedCheck_4565_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_fst_4541_);
lean_dec(v_a_4537_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4565_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
if (lean_obj_tag(v_fst_4541_) == 0)
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
lean_del_object(v___x_4539_);
v___x_4545_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4546_ = l_Lean_MessageData_ofName(v___x_4530_);
lean_inc_ref(v___x_4546_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set_tag(v___x_4543_, 7);
lean_ctor_set(v___x_4543_, 1, v___x_4546_);
lean_ctor_set(v___x_4543_, 0, v___x_4545_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4549_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4548_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4552_ = l_Lean_indentD(v___x_4551_);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4550_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v___x_4546_);
v___x_4557_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4558_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4559_;
}
}
else
{
lean_object* v_val_4561_; lean_object* v___x_4563_; 
lean_del_object(v___x_4543_);
lean_dec(v___x_4530_);
lean_dec(v_stx_2380_);
v_val_4561_ = lean_ctor_get(v_fst_4541_, 0);
lean_inc(v_val_4561_);
lean_dec_ref_known(v_fst_4541_, 1);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v_val_4561_);
v___x_4563_ = v___x_4539_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_val_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec(v___x_4530_);
lean_dec(v_stx_2380_);
v_a_4568_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4536_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4536_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
v___y_4423_ = v_a_2381_;
v___y_4424_ = v_a_2382_;
v___y_4425_ = v_a_2383_;
v___y_4426_ = v_a_2384_;
v___y_4427_ = v_a_2385_;
v___y_4428_ = v_a_2386_;
goto v___jp_4422_;
}
}
else
{
lean_dec(v___x_4527_);
v___y_4423_ = v_a_2381_;
v___y_4424_ = v_a_2382_;
v___y_4425_ = v_a_2383_;
v___y_4426_ = v_a_2384_;
v___y_4427_ = v_a_2385_;
v___y_4428_ = v_a_2386_;
goto v___jp_4422_;
}
v___jp_4422_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4429_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4421_);
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4429_);
v___x_4431_ = l_Lean_Syntax_isOfKind(v___x_4429_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v_env_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec(v___x_4429_);
lean_inc_n(v_stx_2380_, 2);
v___x_4432_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4433_ = lean_st_ref_get(v___y_4428_);
v_env_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc_ref(v_env_4434_);
lean_dec(v___x_4433_);
v___x_4435_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4436_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4435_, v_env_4434_, v___x_4432_);
v___x_4437_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4438_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4436_, v___x_4437_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___x_4436_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4469_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4469_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4469_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v_fst_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4467_; 
v_fst_4443_ = lean_ctor_get(v_a_4439_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_a_4439_);
if (v_isSharedCheck_4467_ == 0)
{
lean_object* v_unused_4468_; 
v_unused_4468_ = lean_ctor_get(v_a_4439_, 1);
lean_dec(v_unused_4468_);
v___x_4445_ = v_a_4439_;
v_isShared_4446_ = v_isSharedCheck_4467_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_fst_4443_);
lean_dec(v_a_4439_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4467_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
if (lean_obj_tag(v_fst_4443_) == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_del_object(v___x_4441_);
v___x_4447_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4448_ = l_Lean_MessageData_ofName(v___x_4432_);
lean_inc_ref(v___x_4448_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set_tag(v___x_4445_, 7);
lean_ctor_set(v___x_4445_, 1, v___x_4448_);
lean_ctor_set(v___x_4445_, 0, v___x_4447_);
v___x_4450_ = v___x_4445_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4447_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4451_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4450_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
v___x_4453_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4454_ = l_Lean_indentD(v___x_4453_);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4452_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
v___x_4456_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4455_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
v___x_4458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
lean_ctor_set(v___x_4458_, 1, v___x_4448_);
v___x_4459_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___x_4461_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4460_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4461_;
}
}
else
{
lean_object* v_val_4463_; lean_object* v___x_4465_; 
lean_del_object(v___x_4445_);
lean_dec(v___x_4432_);
lean_dec(v_stx_2380_);
v_val_4463_ = lean_ctor_get(v_fst_4443_, 0);
lean_inc(v_val_4463_);
lean_dec_ref_known(v_fst_4443_, 1);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v_val_4463_);
v___x_4465_ = v___x_4441_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_val_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v___x_4432_);
lean_dec(v_stx_2380_);
v_a_4470_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4438_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4438_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
else
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = l_Lean_Syntax_getArg(v___x_4429_, v___x_4421_);
lean_dec(v___x_4429_);
v___x_4479_ = l_Lean_Syntax_isNone(v___x_4478_);
if (v___x_4479_ == 0)
{
uint8_t v___x_4480_; 
v___x_4480_ = l_Lean_Syntax_matchesNull(v___x_4478_, v___x_4421_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v_env_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4481_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4482_ = lean_st_ref_get(v___y_4428_);
v_env_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc_ref(v_env_4483_);
lean_dec(v___x_4482_);
v___x_4484_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4485_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4484_, v_env_4483_, v___x_4481_);
v___x_4486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4487_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4485_, v___x_4486_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___x_4485_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4518_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4518_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4518_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_fst_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4516_; 
v_fst_4492_ = lean_ctor_get(v_a_4488_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_a_4488_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; 
v_unused_4517_ = lean_ctor_get(v_a_4488_, 1);
lean_dec(v_unused_4517_);
v___x_4494_ = v_a_4488_;
v_isShared_4495_ = v_isSharedCheck_4516_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_fst_4492_);
lean_dec(v_a_4488_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4516_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
if (lean_obj_tag(v_fst_4492_) == 0)
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
lean_del_object(v___x_4490_);
v___x_4496_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4497_ = l_Lean_MessageData_ofName(v___x_4481_);
lean_inc_ref(v___x_4497_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 7);
lean_ctor_set(v___x_4494_, 1, v___x_4497_);
lean_ctor_set(v___x_4494_, 0, v___x_4496_);
v___x_4499_ = v___x_4494_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v___x_4497_);
v___x_4499_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4500_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4499_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
v___x_4502_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4503_ = l_Lean_indentD(v___x_4502_);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4501_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v___x_4497_);
v___x_4508_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4507_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
v___x_4510_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4509_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4510_;
}
}
else
{
lean_object* v_val_4512_; lean_object* v___x_4514_; 
lean_del_object(v___x_4494_);
lean_dec(v___x_4481_);
lean_dec(v_stx_2380_);
v_val_4512_ = lean_ctor_get(v_fst_4492_, 0);
lean_inc(v_val_4512_);
lean_dec_ref_known(v_fst_4492_, 1);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v_val_4512_);
v___x_4514_ = v___x_4490_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_val_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v___x_4481_);
lean_dec(v_stx_2380_);
v_a_4519_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4487_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4487_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_dec(v_stx_2380_);
goto v___jp_2406_;
}
}
else
{
lean_dec(v___x_4478_);
lean_dec(v_stx_2380_);
goto v___jp_2406_;
}
}
}
}
}
}
else
{
lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4576_ = lean_unsigned_to_nat(1u);
v___x_4577_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4576_);
v___x_4578_ = l_Lean_Syntax_isNone(v___x_4577_);
if (v___x_4578_ == 0)
{
uint8_t v___x_4579_; 
v___x_4579_ = l_Lean_Syntax_matchesNull(v___x_4577_, v___x_4576_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v_env_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4580_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4581_ = lean_st_ref_get(v_a_2386_);
v_env_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc_ref(v_env_4582_);
lean_dec(v___x_4581_);
v___x_4583_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4584_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4583_, v_env_4582_, v___x_4580_);
v___x_4585_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4586_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4584_, v___x_4585_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4584_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4617_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4589_ = v___x_4586_;
v_isShared_4590_ = v_isSharedCheck_4617_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4617_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v_fst_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4615_; 
v_fst_4591_ = lean_ctor_get(v_a_4587_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_a_4587_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; 
v_unused_4616_ = lean_ctor_get(v_a_4587_, 1);
lean_dec(v_unused_4616_);
v___x_4593_ = v_a_4587_;
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_fst_4591_);
lean_dec(v_a_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
if (lean_obj_tag(v_fst_4591_) == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_del_object(v___x_4589_);
v___x_4595_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4596_ = l_Lean_MessageData_ofName(v___x_4580_);
lean_inc_ref(v___x_4596_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 7);
lean_ctor_set(v___x_4593_, 1, v___x_4596_);
lean_ctor_set(v___x_4593_, 0, v___x_4595_);
v___x_4598_ = v___x_4593_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4595_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4599_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4598_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4602_ = l_Lean_indentD(v___x_4601_);
v___x_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4600_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4603_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
v___x_4606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
lean_ctor_set(v___x_4606_, 1, v___x_4596_);
v___x_4607_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4608_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4609_;
}
}
else
{
lean_object* v_val_4611_; lean_object* v___x_4613_; 
lean_del_object(v___x_4593_);
lean_dec(v___x_4580_);
lean_dec(v_stx_2380_);
v_val_4611_ = lean_ctor_get(v_fst_4591_, 0);
lean_inc(v_val_4611_);
lean_dec_ref_known(v_fst_4591_, 1);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v_val_4611_);
v___x_4613_ = v___x_4589_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_val_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_dec(v___x_4580_);
lean_dec(v_stx_2380_);
v_a_4618_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4586_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4586_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
v___y_2638_ = v_a_2381_;
v___y_2639_ = v_a_2382_;
v___y_2640_ = v_a_2383_;
v___y_2641_ = v_a_2384_;
v___y_2642_ = v_a_2385_;
v___y_2643_ = v_a_2386_;
goto v___jp_2637_;
}
}
else
{
lean_dec(v___x_4577_);
v___y_2638_ = v_a_2381_;
v___y_2639_ = v_a_2382_;
v___y_2640_ = v_a_2383_;
v___y_2641_ = v_a_2384_;
v___y_2642_ = v_a_2385_;
v___y_2643_ = v_a_2386_;
goto v___jp_2637_;
}
}
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4626_ = lean_unsigned_to_nat(1u);
v___x_4627_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4626_);
v___x_4628_ = l_Lean_Syntax_isNone(v___x_4627_);
if (v___x_4628_ == 0)
{
uint8_t v___x_4629_; 
v___x_4629_ = l_Lean_Syntax_matchesNull(v___x_4627_, v___x_4626_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v_env_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4630_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4631_ = lean_st_ref_get(v_a_2386_);
v_env_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc_ref(v_env_4632_);
lean_dec(v___x_4631_);
v___x_4633_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4634_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4633_, v_env_4632_, v___x_4630_);
v___x_4635_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4634_, v___x_4635_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4634_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4667_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4667_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4667_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v_fst_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4665_; 
v_fst_4641_ = lean_ctor_get(v_a_4637_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_a_4637_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; 
v_unused_4666_ = lean_ctor_get(v_a_4637_, 1);
lean_dec(v_unused_4666_);
v___x_4643_ = v_a_4637_;
v_isShared_4644_ = v_isSharedCheck_4665_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_fst_4641_);
lean_dec(v_a_4637_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4665_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
if (lean_obj_tag(v_fst_4641_) == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
lean_del_object(v___x_4639_);
v___x_4645_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4646_ = l_Lean_MessageData_ofName(v___x_4630_);
lean_inc_ref(v___x_4646_);
if (v_isShared_4644_ == 0)
{
lean_ctor_set_tag(v___x_4643_, 7);
lean_ctor_set(v___x_4643_, 1, v___x_4646_);
lean_ctor_set(v___x_4643_, 0, v___x_4645_);
v___x_4648_ = v___x_4643_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4649_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
v___x_4651_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4652_ = l_Lean_indentD(v___x_4651_);
v___x_4653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4650_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
v___x_4654_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
lean_ctor_set(v___x_4656_, 1, v___x_4646_);
v___x_4657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4658_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4659_;
}
}
else
{
lean_object* v_val_4661_; lean_object* v___x_4663_; 
lean_del_object(v___x_4643_);
lean_dec(v___x_4630_);
lean_dec(v_stx_2380_);
v_val_4661_ = lean_ctor_get(v_fst_4641_, 0);
lean_inc(v_val_4661_);
lean_dec_ref_known(v_fst_4641_, 1);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v_val_4661_);
v___x_4663_ = v___x_4639_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_val_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_dec(v___x_4630_);
lean_dec(v_stx_2380_);
v_a_4668_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4636_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4636_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
else
{
v___y_2437_ = v_a_2381_;
v___y_2438_ = v_a_2382_;
v___y_2439_ = v_a_2383_;
v___y_2440_ = v_a_2384_;
v___y_2441_ = v_a_2385_;
v___y_2442_ = v_a_2386_;
goto v___jp_2436_;
}
}
else
{
lean_dec(v___x_4627_);
v___y_2437_ = v_a_2381_;
v___y_2438_ = v_a_2382_;
v___y_2439_ = v_a_2383_;
v___y_2440_ = v_a_2384_;
v___y_2441_ = v_a_2385_;
v___y_2442_ = v_a_2386_;
goto v___jp_2436_;
}
}
v___jp_2637_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2644_ = lean_unsigned_to_nat(2u);
v___x_2645_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2644_);
v___x_2646_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2647_ = l_Lean_Syntax_isOfKind(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_inc_n(v_stx_2380_, 2);
v___x_2648_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2649_ = lean_st_ref_get(v___y_2643_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2651_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2652_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2651_, v_env_2650_, v___x_2648_);
v___x_2653_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2654_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2652_, v___x_2653_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___x_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2685_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2685_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_fst_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2683_; 
v_fst_2659_ = lean_ctor_get(v_a_2655_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v_a_2655_, 1);
lean_dec(v_unused_2684_);
v___x_2661_ = v_a_2655_;
v_isShared_2662_ = v_isSharedCheck_2683_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_fst_2659_);
lean_dec(v_a_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2683_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
if (lean_obj_tag(v_fst_2659_) == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
lean_del_object(v___x_2657_);
v___x_2663_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2664_ = l_Lean_MessageData_ofName(v___x_2648_);
lean_inc_ref(v___x_2664_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 7);
lean_ctor_set(v___x_2661_, 1, v___x_2664_);
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2670_ = l_Lean_indentD(v___x_2669_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2668_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
lean_ctor_set(v___x_2674_, 1, v___x_2664_);
v___x_2675_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2676_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2677_;
}
}
else
{
lean_object* v_val_2679_; lean_object* v___x_2681_; 
lean_del_object(v___x_2661_);
lean_dec(v___x_2648_);
lean_dec(v_stx_2380_);
v_val_2679_ = lean_ctor_get(v_fst_2659_, 0);
lean_inc(v_val_2679_);
lean_dec_ref_known(v_fst_2659_, 1);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v_val_2679_);
v___x_2681_ = v___x_2657_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_val_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v___x_2648_);
lean_dec(v_stx_2380_);
v_a_2686_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2654_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2654_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_unsigned_to_nat(3u);
v___x_2695_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2694_);
lean_dec(v_stx_2380_);
v___x_2696_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2636_, v___x_2695_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2696_;
}
}
}
else
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v___x_4676_ = lean_unsigned_to_nat(0u);
v___x_4677_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4676_);
v___x_4678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4679_ = l_Lean_Syntax_isOfKind(v___x_4677_, v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v_env_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4680_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4681_ = lean_st_ref_get(v_a_2386_);
v_env_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc_ref(v_env_4682_);
lean_dec(v___x_4681_);
v___x_4683_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4684_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4683_, v_env_4682_, v___x_4680_);
v___x_4685_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4686_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4684_, v___x_4685_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4684_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4717_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4717_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4717_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v_fst_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4715_; 
v_fst_4691_ = lean_ctor_get(v_a_4687_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_a_4687_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; 
v_unused_4716_ = lean_ctor_get(v_a_4687_, 1);
lean_dec(v_unused_4716_);
v___x_4693_ = v_a_4687_;
v_isShared_4694_ = v_isSharedCheck_4715_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_fst_4691_);
lean_dec(v_a_4687_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4715_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
if (lean_obj_tag(v_fst_4691_) == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
lean_del_object(v___x_4689_);
v___x_4695_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4696_ = l_Lean_MessageData_ofName(v___x_4680_);
lean_inc_ref(v___x_4696_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set_tag(v___x_4693_, 7);
lean_ctor_set(v___x_4693_, 1, v___x_4696_);
lean_ctor_set(v___x_4693_, 0, v___x_4695_);
v___x_4698_ = v___x_4693_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4710_, 1, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4698_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4702_ = l_Lean_indentD(v___x_4701_);
v___x_4703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4700_);
lean_ctor_set(v___x_4703_, 1, v___x_4702_);
v___x_4704_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4703_);
lean_ctor_set(v___x_4705_, 1, v___x_4704_);
v___x_4706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set(v___x_4706_, 1, v___x_4696_);
v___x_4707_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4706_);
lean_ctor_set(v___x_4708_, 1, v___x_4707_);
v___x_4709_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4708_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4709_;
}
}
else
{
lean_object* v_val_4711_; lean_object* v___x_4713_; 
lean_del_object(v___x_4693_);
lean_dec(v___x_4680_);
lean_dec(v_stx_2380_);
v_val_4711_ = lean_ctor_get(v_fst_4691_, 0);
lean_inc(v_val_4711_);
lean_dec_ref_known(v_fst_4691_, 1);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v_val_4711_);
v___x_4713_ = v___x_4689_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_val_4711_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec(v___x_4680_);
lean_dec(v_stx_2380_);
v_a_4718_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4686_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4686_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4726_ = lean_unsigned_to_nat(1u);
v___x_4727_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4726_);
v___x_4728_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4727_);
v___x_4729_ = l_Lean_Syntax_isOfKind(v___x_4727_, v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v_env_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
lean_dec(v___x_4727_);
lean_inc_n(v_stx_2380_, 2);
v___x_4730_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4731_ = lean_st_ref_get(v_a_2386_);
v_env_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc_ref(v_env_4732_);
lean_dec(v___x_4731_);
v___x_4733_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4734_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4733_, v_env_4732_, v___x_4730_);
v___x_4735_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4736_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4734_, v___x_4735_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4734_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4767_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_fst_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4765_; 
v_fst_4741_ = lean_ctor_get(v_a_4737_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v_a_4737_);
if (v_isSharedCheck_4765_ == 0)
{
lean_object* v_unused_4766_; 
v_unused_4766_ = lean_ctor_get(v_a_4737_, 1);
lean_dec(v_unused_4766_);
v___x_4743_ = v_a_4737_;
v_isShared_4744_ = v_isSharedCheck_4765_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_fst_4741_);
lean_dec(v_a_4737_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4765_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
if (lean_obj_tag(v_fst_4741_) == 0)
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4748_; 
lean_del_object(v___x_4739_);
v___x_4745_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4746_ = l_Lean_MessageData_ofName(v___x_4730_);
lean_inc_ref(v___x_4746_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set_tag(v___x_4743_, 7);
lean_ctor_set(v___x_4743_, 1, v___x_4746_);
lean_ctor_set(v___x_4743_, 0, v___x_4745_);
v___x_4748_ = v___x_4743_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4749_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4752_ = l_Lean_indentD(v___x_4751_);
v___x_4753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4750_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4753_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
lean_ctor_set(v___x_4756_, 1, v___x_4746_);
v___x_4757_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4758_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4759_;
}
}
else
{
lean_object* v_val_4761_; lean_object* v___x_4763_; 
lean_del_object(v___x_4743_);
lean_dec(v___x_4730_);
lean_dec(v_stx_2380_);
v_val_4761_ = lean_ctor_get(v_fst_4741_, 0);
lean_inc(v_val_4761_);
lean_dec_ref_known(v_fst_4741_, 1);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v_val_4761_);
v___x_4763_ = v___x_4739_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_val_4761_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v___x_4730_);
lean_dec(v_stx_2380_);
v_a_4768_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4736_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4736_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v___x_4776_; uint8_t v___x_4777_; 
v___x_4776_ = l_Lean_Syntax_getArg(v___x_4727_, v___x_4676_);
lean_dec(v___x_4727_);
lean_inc(v___x_4776_);
v___x_4777_ = l_Lean_Syntax_matchesNull(v___x_4776_, v___x_4726_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v_env_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
lean_dec(v___x_4776_);
lean_inc_n(v_stx_2380_, 2);
v___x_4778_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4779_ = lean_st_ref_get(v_a_2386_);
v_env_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_ref(v_env_4780_);
lean_dec(v___x_4779_);
v___x_4781_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4782_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4781_, v_env_4780_, v___x_4778_);
v___x_4783_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4784_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4782_, v___x_4783_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4782_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4815_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4815_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4815_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_fst_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4813_; 
v_fst_4789_ = lean_ctor_get(v_a_4785_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_a_4785_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v_a_4785_, 1);
lean_dec(v_unused_4814_);
v___x_4791_ = v_a_4785_;
v_isShared_4792_ = v_isSharedCheck_4813_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_fst_4789_);
lean_dec(v_a_4785_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4813_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
if (lean_obj_tag(v_fst_4789_) == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4796_; 
lean_del_object(v___x_4787_);
v___x_4793_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4794_ = l_Lean_MessageData_ofName(v___x_4778_);
lean_inc_ref(v___x_4794_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set_tag(v___x_4791_, 7);
lean_ctor_set(v___x_4791_, 1, v___x_4794_);
lean_ctor_set(v___x_4791_, 0, v___x_4793_);
v___x_4796_ = v___x_4791_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4793_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4796_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4800_ = l_Lean_indentD(v___x_4799_);
v___x_4801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4798_);
lean_ctor_set(v___x_4801_, 1, v___x_4800_);
v___x_4802_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4801_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
lean_ctor_set(v___x_4804_, 1, v___x_4794_);
v___x_4805_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4804_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4806_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4807_;
}
}
else
{
lean_object* v_val_4809_; lean_object* v___x_4811_; 
lean_del_object(v___x_4791_);
lean_dec(v___x_4778_);
lean_dec(v_stx_2380_);
v_val_4809_ = lean_ctor_get(v_fst_4789_, 0);
lean_inc(v_val_4809_);
lean_dec_ref_known(v_fst_4789_, 1);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v_val_4809_);
v___x_4811_ = v___x_4787_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_val_4809_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v___x_4778_);
lean_dec(v_stx_2380_);
v_a_4816_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4784_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4784_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v___x_4824_ = l_Lean_Syntax_getArg(v___x_4776_, v___x_4676_);
lean_dec(v___x_4776_);
v___x_4825_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4826_ = l_Lean_Syntax_isOfKind(v___x_4824_, v___x_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v_env_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4827_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4828_ = lean_st_ref_get(v_a_2386_);
v_env_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc_ref(v_env_4829_);
lean_dec(v___x_4828_);
v___x_4830_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4831_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4830_, v_env_4829_, v___x_4827_);
v___x_4832_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4833_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4831_, v___x_4832_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4831_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4864_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4864_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4864_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v_fst_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4862_; 
v_fst_4838_ = lean_ctor_get(v_a_4834_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_a_4834_);
if (v_isSharedCheck_4862_ == 0)
{
lean_object* v_unused_4863_; 
v_unused_4863_ = lean_ctor_get(v_a_4834_, 1);
lean_dec(v_unused_4863_);
v___x_4840_ = v_a_4834_;
v_isShared_4841_ = v_isSharedCheck_4862_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_fst_4838_);
lean_dec(v_a_4834_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4862_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
if (lean_obj_tag(v_fst_4838_) == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4845_; 
lean_del_object(v___x_4836_);
v___x_4842_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4843_ = l_Lean_MessageData_ofName(v___x_4827_);
lean_inc_ref(v___x_4843_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set_tag(v___x_4840_, 7);
lean_ctor_set(v___x_4840_, 1, v___x_4843_);
lean_ctor_set(v___x_4840_, 0, v___x_4842_);
v___x_4845_ = v___x_4840_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4846_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4845_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
v___x_4848_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4849_ = l_Lean_indentD(v___x_4848_);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4847_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
lean_ctor_set(v___x_4853_, 1, v___x_4843_);
v___x_4854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4853_);
lean_ctor_set(v___x_4855_, 1, v___x_4854_);
v___x_4856_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4855_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4856_;
}
}
else
{
lean_object* v_val_4858_; lean_object* v___x_4860_; 
lean_del_object(v___x_4840_);
lean_dec(v___x_4827_);
lean_dec(v_stx_2380_);
v_val_4858_ = lean_ctor_get(v_fst_4838_, 0);
lean_inc(v_val_4858_);
lean_dec_ref_known(v_fst_4838_, 1);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v_val_4858_);
v___x_4860_ = v___x_4836_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_val_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
lean_dec(v___x_4827_);
lean_dec(v_stx_2380_);
v_a_4865_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4833_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4833_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
lean_dec(v_stx_2380_);
v___x_4873_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
}
}
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4875_ = lean_unsigned_to_nat(1u);
v___x_4876_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4875_);
v___x_4877_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4878_ = l_Lean_Syntax_isOfKind(v___x_4876_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v_env_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4879_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4880_ = lean_st_ref_get(v_a_2386_);
v_env_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc_ref(v_env_4881_);
lean_dec(v___x_4880_);
v___x_4882_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4883_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4882_, v_env_4881_, v___x_4879_);
v___x_4884_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4885_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4883_, v___x_4884_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4883_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4916_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4916_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4916_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v_fst_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4914_; 
v_fst_4890_ = lean_ctor_get(v_a_4886_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v_a_4886_);
if (v_isSharedCheck_4914_ == 0)
{
lean_object* v_unused_4915_; 
v_unused_4915_ = lean_ctor_get(v_a_4886_, 1);
lean_dec(v_unused_4915_);
v___x_4892_ = v_a_4886_;
v_isShared_4893_ = v_isSharedCheck_4914_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_fst_4890_);
lean_dec(v_a_4886_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4914_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
if (lean_obj_tag(v_fst_4890_) == 0)
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4897_; 
lean_del_object(v___x_4888_);
v___x_4894_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4895_ = l_Lean_MessageData_ofName(v___x_4879_);
lean_inc_ref(v___x_4895_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set_tag(v___x_4892_, 7);
lean_ctor_set(v___x_4892_, 1, v___x_4895_);
lean_ctor_set(v___x_4892_, 0, v___x_4894_);
v___x_4897_ = v___x_4892_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v___x_4895_);
v___x_4897_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4898_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4897_);
lean_ctor_set(v___x_4899_, 1, v___x_4898_);
v___x_4900_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4901_ = l_Lean_indentD(v___x_4900_);
v___x_4902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4899_);
lean_ctor_set(v___x_4902_, 1, v___x_4901_);
v___x_4903_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
lean_ctor_set(v___x_4905_, 1, v___x_4895_);
v___x_4906_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4905_);
lean_ctor_set(v___x_4907_, 1, v___x_4906_);
v___x_4908_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4907_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4908_;
}
}
else
{
lean_object* v_val_4910_; lean_object* v___x_4912_; 
lean_del_object(v___x_4892_);
lean_dec(v___x_4879_);
lean_dec(v_stx_2380_);
v_val_4910_ = lean_ctor_get(v_fst_4890_, 0);
lean_inc(v_val_4910_);
lean_dec_ref_known(v_fst_4890_, 1);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v_val_4910_);
v___x_4912_ = v___x_4888_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_val_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec(v___x_4879_);
lean_dec(v_stx_2380_);
v_a_4917_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4885_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4885_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; uint8_t v___x_4928_; 
v___x_4925_ = lean_unsigned_to_nat(2u);
v___x_4926_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4925_);
v___x_4927_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4928_ = l_Lean_Syntax_isOfKind(v___x_4926_, v___x_4927_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v_env_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_inc_n(v_stx_2380_, 2);
v___x_4929_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4930_ = lean_st_ref_get(v_a_2386_);
v_env_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc_ref(v_env_4931_);
lean_dec(v___x_4930_);
v___x_4932_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4933_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4932_, v_env_4931_, v___x_4929_);
v___x_4934_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4935_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4933_, v___x_4934_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4933_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4966_; 
v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4935_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4938_ = v___x_4935_;
v_isShared_4939_ = v_isSharedCheck_4966_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4935_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4966_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v_fst_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4964_; 
v_fst_4940_ = lean_ctor_get(v_a_4936_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_a_4936_);
if (v_isSharedCheck_4964_ == 0)
{
lean_object* v_unused_4965_; 
v_unused_4965_ = lean_ctor_get(v_a_4936_, 1);
lean_dec(v_unused_4965_);
v___x_4942_ = v_a_4936_;
v_isShared_4943_ = v_isSharedCheck_4964_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_fst_4940_);
lean_dec(v_a_4936_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4964_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
if (lean_obj_tag(v_fst_4940_) == 0)
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_del_object(v___x_4938_);
v___x_4944_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4945_ = l_Lean_MessageData_ofName(v___x_4929_);
lean_inc_ref(v___x_4945_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set_tag(v___x_4942_, 7);
lean_ctor_set(v___x_4942_, 1, v___x_4945_);
lean_ctor_set(v___x_4942_, 0, v___x_4944_);
v___x_4947_ = v___x_4942_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4944_);
lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4948_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_4951_ = l_Lean_indentD(v___x_4950_);
v___x_4952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4949_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
v___x_4953_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4952_);
lean_ctor_set(v___x_4954_, 1, v___x_4953_);
v___x_4955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v___x_4945_);
v___x_4956_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4957_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_4958_;
}
}
else
{
lean_object* v_val_4960_; lean_object* v___x_4962_; 
lean_del_object(v___x_4942_);
lean_dec(v___x_4929_);
lean_dec(v_stx_2380_);
v_val_4960_ = lean_ctor_get(v_fst_4940_, 0);
lean_inc(v_val_4960_);
lean_dec_ref_known(v_fst_4940_, 1);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v_val_4960_);
v___x_4962_ = v___x_4938_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_val_4960_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec(v___x_4929_);
lean_dec(v_stx_2380_);
v_a_4967_ = lean_ctor_get(v___x_4935_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4935_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4935_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4935_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
else
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
lean_dec(v_stx_2380_);
v___x_4975_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
return v___x_4976_;
}
}
}
}
else
{
lean_object* v___x_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v___x_4977_ = lean_unsigned_to_nat(1u);
v___x_4978_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_4977_);
v___x_4979_ = l_Lean_Syntax_isNone(v___x_4978_);
if (v___x_4979_ == 0)
{
uint8_t v___x_4980_; 
v___x_4980_ = l_Lean_Syntax_matchesNull(v___x_4978_, v___x_4977_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v_env_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_del_object(v___x_2420_);
lean_inc_n(v_stx_2380_, 2);
v___x_4981_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_4982_ = lean_st_ref_get(v_a_2386_);
v_env_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc_ref(v_env_4983_);
lean_dec(v___x_4982_);
v___x_4984_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4985_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4984_, v_env_4983_, v___x_4981_);
v___x_4986_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4987_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_4985_, v___x_4986_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_4985_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_5018_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4990_ = v___x_4987_;
v_isShared_4991_ = v_isSharedCheck_5018_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4987_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_5018_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v_fst_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5016_; 
v_fst_4992_ = lean_ctor_get(v_a_4988_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_a_4988_);
if (v_isSharedCheck_5016_ == 0)
{
lean_object* v_unused_5017_; 
v_unused_5017_ = lean_ctor_get(v_a_4988_, 1);
lean_dec(v_unused_5017_);
v___x_4994_ = v_a_4988_;
v_isShared_4995_ = v_isSharedCheck_5016_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_fst_4992_);
lean_dec(v_a_4988_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5016_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
if (lean_obj_tag(v_fst_4992_) == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4999_; 
lean_del_object(v___x_4990_);
v___x_4996_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4997_ = l_Lean_MessageData_ofName(v___x_4981_);
lean_inc_ref(v___x_4997_);
if (v_isShared_4995_ == 0)
{
lean_ctor_set_tag(v___x_4994_, 7);
lean_ctor_set(v___x_4994_, 1, v___x_4997_);
lean_ctor_set(v___x_4994_, 0, v___x_4996_);
v___x_4999_ = v___x_4994_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5011_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5000_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_5001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_5003_ = l_Lean_indentD(v___x_5002_);
v___x_5004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5001_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
v___x_5005_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_5006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5004_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
v___x_5007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5006_);
lean_ctor_set(v___x_5007_, 1, v___x_4997_);
v___x_5008_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_5009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5007_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5009_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_5010_;
}
}
else
{
lean_object* v_val_5012_; lean_object* v___x_5014_; 
lean_del_object(v___x_4994_);
lean_dec(v___x_4981_);
lean_dec(v_stx_2380_);
v_val_5012_ = lean_ctor_get(v_fst_4992_, 0);
lean_inc(v_val_5012_);
lean_dec_ref_known(v_fst_4992_, 1);
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_val_5012_);
v___x_5014_ = v___x_4990_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_val_5012_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec(v___x_4981_);
lean_dec(v_stx_2380_);
v_a_5019_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4987_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4987_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
else
{
v___y_2508_ = v_a_2381_;
v___y_2509_ = v_a_2382_;
v___y_2510_ = v_a_2383_;
v___y_2511_ = v_a_2384_;
v___y_2512_ = v_a_2385_;
v___y_2513_ = v_a_2386_;
goto v___jp_2507_;
}
}
else
{
lean_dec(v___x_4978_);
v___y_2508_ = v_a_2381_;
v___y_2509_ = v_a_2382_;
v___y_2510_ = v_a_2383_;
v___y_2511_ = v_a_2384_;
v___y_2512_ = v_a_2385_;
v___y_2513_ = v_a_2386_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
lean_del_object(v___x_2420_);
v___x_5027_ = lean_unsigned_to_nat(1u);
v___x_5028_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_5027_);
lean_dec(v_stx_2380_);
v___x_5029_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5028_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_5029_;
}
}
else
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
lean_del_object(v___x_2420_);
v___x_5030_ = lean_unsigned_to_nat(0u);
v___x_5031_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_5030_);
lean_dec(v_stx_2380_);
v___x_5032_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5031_);
if (lean_obj_tag(v___x_5032_) == 1)
{
lean_object* v_val_5033_; lean_object* v_snd_5034_; lean_object* v_body_5035_; lean_object* v___x_5036_; 
v_val_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_val_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v_snd_5034_ = lean_ctor_get(v_val_5033_, 1);
lean_inc(v_snd_5034_);
lean_dec(v_val_5033_);
v_body_5035_ = lean_ctor_get(v_snd_5034_, 1);
lean_inc(v_body_5035_);
lean_dec(v_snd_5034_);
v___x_5036_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5035_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5057_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5057_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5057_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
uint8_t v_breaks_5041_; uint8_t v_continues_5042_; uint8_t v_returnsEarly_5043_; lean_object* v_reassigns_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5055_; 
v_breaks_5041_ = lean_ctor_get_uint8(v_a_5037_, sizeof(void*)*2);
v_continues_5042_ = lean_ctor_get_uint8(v_a_5037_, sizeof(void*)*2 + 1);
v_returnsEarly_5043_ = lean_ctor_get_uint8(v_a_5037_, sizeof(void*)*2 + 2);
v_reassigns_5044_ = lean_ctor_get(v_a_5037_, 1);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_a_5037_);
if (v_isSharedCheck_5055_ == 0)
{
lean_object* v_unused_5056_; 
v_unused_5056_ = lean_ctor_get(v_a_5037_, 0);
lean_dec(v_unused_5056_);
v___x_5046_ = v_a_5037_;
v_isShared_5047_ = v_isSharedCheck_5055_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_reassigns_5044_);
lean_dec(v_a_5037_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5055_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5048_; lean_object* v___x_5050_; 
v___x_5048_ = lean_unsigned_to_nat(1u);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v___x_5048_);
v___x_5050_ = v___x_5046_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5048_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v_reassigns_5044_);
lean_ctor_set_uint8(v_reuseFailAlloc_5054_, sizeof(void*)*2, v_breaks_5041_);
lean_ctor_set_uint8(v_reuseFailAlloc_5054_, sizeof(void*)*2 + 1, v_continues_5042_);
lean_ctor_set_uint8(v_reuseFailAlloc_5054_, sizeof(void*)*2 + 2, v_returnsEarly_5043_);
v___x_5050_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5052_; 
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*2 + 3, v___x_2624_);
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5050_);
v___x_5052_ = v___x_5039_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
else
{
return v___x_5036_;
}
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
lean_dec(v___x_5032_);
v___x_5058_ = lean_unsigned_to_nat(1u);
v___x_5059_ = l_Lean_NameSet_empty;
v___x_5060_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5060_, 0, v___x_5058_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
lean_ctor_set_uint8(v___x_5060_, sizeof(void*)*2, v___x_2624_);
lean_ctor_set_uint8(v___x_5060_, sizeof(void*)*2 + 1, v___x_2624_);
lean_ctor_set_uint8(v___x_5060_, sizeof(void*)*2 + 2, v___x_2624_);
lean_ctor_set_uint8(v___x_5060_, sizeof(void*)*2 + 3, v___x_2624_);
v___x_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5060_);
return v___x_5061_;
}
}
}
else
{
lean_object* v___x_5062_; lean_object* v___x_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; 
lean_del_object(v___x_2420_);
v___x_5062_ = lean_unsigned_to_nat(0u);
v___x_5067_ = lean_unsigned_to_nat(1u);
v___x_5068_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_5067_);
v___x_5069_ = l_Lean_Syntax_isNone(v___x_5068_);
if (v___x_5069_ == 0)
{
uint8_t v___x_5070_; 
v___x_5070_ = l_Lean_Syntax_matchesNull(v___x_5068_, v___x_5067_);
if (v___x_5070_ == 0)
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_env_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
lean_inc_n(v_stx_2380_, 2);
v___x_5071_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_5072_ = lean_st_ref_get(v_a_2386_);
v_env_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc_ref(v_env_5073_);
lean_dec(v___x_5072_);
v___x_5074_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5075_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5074_, v_env_5073_, v___x_5071_);
v___x_5076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5077_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_5075_, v___x_5076_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v___x_5075_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5108_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5108_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5108_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v_fst_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5106_; 
v_fst_5082_ = lean_ctor_get(v_a_5078_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_a_5078_);
if (v_isSharedCheck_5106_ == 0)
{
lean_object* v_unused_5107_; 
v_unused_5107_ = lean_ctor_get(v_a_5078_, 1);
lean_dec(v_unused_5107_);
v___x_5084_ = v_a_5078_;
v_isShared_5085_ = v_isSharedCheck_5106_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_fst_5082_);
lean_dec(v_a_5078_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5106_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
if (lean_obj_tag(v_fst_5082_) == 0)
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5089_; 
lean_del_object(v___x_5080_);
v___x_5086_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_5087_ = l_Lean_MessageData_ofName(v___x_5071_);
lean_inc_ref(v___x_5087_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 7);
lean_ctor_set(v___x_5084_, 1, v___x_5087_);
lean_ctor_set(v___x_5084_, 0, v___x_5086_);
v___x_5089_ = v___x_5084_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5090_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5089_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_5093_ = l_Lean_indentD(v___x_5092_);
v___x_5094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5091_);
lean_ctor_set(v___x_5094_, 1, v___x_5093_);
v___x_5095_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_5096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5094_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
v___x_5097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
lean_ctor_set(v___x_5097_, 1, v___x_5087_);
v___x_5098_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_5099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5099_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v___x_5100_;
}
}
else
{
lean_object* v_val_5102_; lean_object* v___x_5104_; 
lean_del_object(v___x_5084_);
lean_dec(v___x_5071_);
lean_dec(v_stx_2380_);
v_val_5102_ = lean_ctor_get(v_fst_5082_, 0);
lean_inc(v_val_5102_);
lean_dec_ref_known(v_fst_5082_, 1);
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 0, v_val_5102_);
v___x_5104_ = v___x_5080_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_val_5102_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v___x_5071_);
lean_dec(v_stx_2380_);
v_a_5109_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5077_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5077_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
else
{
lean_dec(v_stx_2380_);
goto v___jp_5063_;
}
}
else
{
lean_dec(v___x_5068_);
lean_dec(v_stx_2380_);
goto v___jp_5063_;
}
v___jp_5063_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5064_ = l_Lean_NameSet_empty;
v___x_5065_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5065_, 0, v___x_5062_);
lean_ctor_set(v___x_5065_, 1, v___x_5064_);
lean_ctor_set_uint8(v___x_5065_, sizeof(void*)*2, v___x_2622_);
lean_ctor_set_uint8(v___x_5065_, sizeof(void*)*2 + 1, v___x_2622_);
lean_ctor_set_uint8(v___x_5065_, sizeof(void*)*2 + 2, v___x_2620_);
lean_ctor_set_uint8(v___x_5065_, sizeof(void*)*2 + 3, v___x_2620_);
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
return v___x_5066_;
}
}
}
else
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
lean_del_object(v___x_2420_);
lean_dec(v_stx_2380_);
v___x_5117_ = lean_unsigned_to_nat(0u);
v___x_5118_ = l_Lean_NameSet_empty;
v___x_5119_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5119_, 0, v___x_5117_);
lean_ctor_set(v___x_5119_, 1, v___x_5118_);
lean_ctor_set_uint8(v___x_5119_, sizeof(void*)*2, v___x_2619_);
lean_ctor_set_uint8(v___x_5119_, sizeof(void*)*2 + 1, v___x_2620_);
lean_ctor_set_uint8(v___x_5119_, sizeof(void*)*2 + 2, v___x_2619_);
lean_ctor_set_uint8(v___x_5119_, sizeof(void*)*2 + 3, v___x_2620_);
v___x_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5119_);
return v___x_5120_;
}
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; 
lean_del_object(v___x_2420_);
lean_dec(v_stx_2380_);
v___x_5121_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
return v___x_5122_;
}
v___jp_2436_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2443_ = lean_unsigned_to_nat(2u);
v___x_2444_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2446_ = l_Lean_Syntax_isOfKind(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_env_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_inc_n(v_stx_2380_, 2);
v___x_2447_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2448_ = lean_st_ref_get(v___y_2442_);
v_env_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_env_2449_);
lean_dec(v___x_2448_);
v___x_2450_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2451_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2450_, v_env_2449_, v___x_2447_);
v___x_2452_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2453_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2451_, v___x_2452_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___x_2451_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2484_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2484_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2484_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_fst_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2482_; 
v_fst_2458_ = lean_ctor_get(v_a_2454_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_a_2454_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; 
v_unused_2483_ = lean_ctor_get(v_a_2454_, 1);
lean_dec(v_unused_2483_);
v___x_2460_ = v_a_2454_;
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_fst_2458_);
lean_dec(v_a_2454_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
if (lean_obj_tag(v_fst_2458_) == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_del_object(v___x_2456_);
v___x_2462_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2463_ = l_Lean_MessageData_ofName(v___x_2447_);
lean_inc_ref(v___x_2463_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 7);
lean_ctor_set(v___x_2460_, 1, v___x_2463_);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2466_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2469_ = l_Lean_indentD(v___x_2468_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2467_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2463_);
v___x_2474_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2475_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2476_;
}
}
else
{
lean_object* v_val_2478_; lean_object* v___x_2480_; 
lean_del_object(v___x_2460_);
lean_dec(v___x_2447_);
lean_dec(v_stx_2380_);
v_val_2478_ = lean_ctor_get(v_fst_2458_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v_fst_2458_, 1);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_val_2478_);
v___x_2480_ = v___x_2456_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_val_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v___x_2447_);
lean_dec(v_stx_2380_);
v_a_2485_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2453_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2453_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2493_ = lean_unsigned_to_nat(7u);
v___x_2494_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2493_);
v___x_2495_ = lean_unsigned_to_nat(8u);
v___x_2496_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2495_);
lean_dec(v_stx_2380_);
v___x_2497_ = l_Lean_Syntax_getOptional_x3f(v___x_2496_);
lean_dec(v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_box(0);
v___y_2394_ = v___y_2439_;
v___y_2395_ = v___y_2441_;
v___y_2396_ = v___x_2494_;
v___y_2397_ = v___y_2438_;
v___y_2398_ = v___y_2437_;
v___y_2399_ = v___y_2440_;
v___y_2400_ = v___y_2442_;
v___y_2401_ = v___x_2498_;
goto v___jp_2393_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_val_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_val_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_val_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
v___y_2394_ = v___y_2439_;
v___y_2395_ = v___y_2441_;
v___y_2396_ = v___x_2494_;
v___y_2397_ = v___y_2438_;
v___y_2398_ = v___y_2437_;
v___y_2399_ = v___y_2440_;
v___y_2400_ = v___y_2442_;
v___y_2401_ = v___x_2504_;
goto v___jp_2393_;
}
}
}
}
}
v___jp_2507_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2514_ = lean_unsigned_to_nat(2u);
v___x_2515_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2517_ = l_Lean_Syntax_isOfKind(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v_env_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_del_object(v___x_2420_);
lean_inc_n(v_stx_2380_, 2);
v___x_2518_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2519_ = lean_st_ref_get(v___y_2513_);
v_env_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_env_2520_);
lean_dec(v___x_2519_);
v___x_2521_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2522_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2521_, v_env_2520_, v___x_2518_);
v___x_2523_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2524_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2522_, v___x_2523_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___x_2522_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2555_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2555_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2555_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_fst_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2553_; 
v_fst_2529_ = lean_ctor_get(v_a_2525_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_a_2525_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v_a_2525_, 1);
lean_dec(v_unused_2554_);
v___x_2531_ = v_a_2525_;
v_isShared_2532_ = v_isSharedCheck_2553_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_fst_2529_);
lean_dec(v_a_2525_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2553_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
if (lean_obj_tag(v_fst_2529_) == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_del_object(v___x_2527_);
v___x_2533_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2534_ = l_Lean_MessageData_ofName(v___x_2518_);
lean_inc_ref(v___x_2534_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set_tag(v___x_2531_, 7);
lean_ctor_set(v___x_2531_, 1, v___x_2534_);
lean_ctor_set(v___x_2531_, 0, v___x_2533_);
v___x_2536_ = v___x_2531_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2537_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2540_ = l_Lean_indentD(v___x_2539_);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2538_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2534_);
v___x_2545_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2546_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2547_;
}
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2551_; 
lean_del_object(v___x_2531_);
lean_dec(v___x_2518_);
lean_dec(v_stx_2380_);
v_val_2549_ = lean_ctor_get(v_fst_2529_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v_fst_2529_, 1);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_val_2549_);
v___x_2551_ = v___x_2527_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_val_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v___x_2518_);
lean_dec(v_stx_2380_);
v_a_2556_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2524_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2524_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2564_ = lean_unsigned_to_nat(3u);
v___x_2565_ = l_Lean_Syntax_getArg(v_stx_2380_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2567_ = l_Lean_Syntax_isOfKind(v___x_2565_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_env_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_del_object(v___x_2420_);
lean_inc_n(v_stx_2380_, 2);
v___x_2568_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2569_ = lean_st_ref_get(v___y_2513_);
v_env_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_env_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2572_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2571_, v_env_2570_, v___x_2568_);
v___x_2573_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2574_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2380_, v___x_2572_, v___x_2573_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___x_2572_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2605_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2605_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2605_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_fst_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2603_; 
v_fst_2579_ = lean_ctor_get(v_a_2575_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_a_2575_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v_a_2575_, 1);
lean_dec(v_unused_2604_);
v___x_2581_ = v_a_2575_;
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_fst_2579_);
lean_dec(v_a_2575_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_fst_2579_) == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_del_object(v___x_2577_);
v___x_2583_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2584_ = l_Lean_MessageData_ofName(v___x_2568_);
lean_inc_ref(v___x_2584_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 7);
lean_ctor_set(v___x_2581_, 1, v___x_2584_);
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2586_ = v___x_2581_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2587_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_MessageData_ofSyntax(v_stx_2380_);
v___x_2590_ = l_Lean_indentD(v___x_2589_);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2584_);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2596_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2597_;
}
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2601_; 
lean_del_object(v___x_2581_);
lean_dec(v___x_2568_);
lean_dec(v_stx_2380_);
v_val_2599_ = lean_ctor_get(v_fst_2579_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v_fst_2579_, 1);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v_val_2599_);
v___x_2601_ = v___x_2577_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_val_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v___x_2568_);
lean_dec(v_stx_2380_);
v_a_2606_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2574_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2574_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_stx_2380_);
v___x_2614_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2614_);
v___x_2616_ = v___x_2420_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
lean_dec(v_stx_2380_);
v_a_5124_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_2417_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_2417_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
v___jp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2389_, v_bodyInfo_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
v___jp_2393_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2403_ = lean_box(0);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___y_2396_);
v___x_2405_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2402_, v___x_2403_, v___x_2404_, v___y_2401_, v___y_2398_, v___y_2397_, v___y_2394_, v___y_2399_, v___y_2395_, v___y_2400_);
return v___x_2405_;
}
v___jp_2406_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
v___jp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2410_, v_bodyInfo_2411_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5132_, size_t v_sz_5133_, size_t v_i_5134_, lean_object* v_b_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
uint8_t v___x_5143_; 
v___x_5143_ = lean_usize_dec_lt(v_i_5134_, v_sz_5133_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
v___x_5144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5144_, 0, v_b_5135_);
return v___x_5144_;
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_array_uget_borrowed(v_as_5132_, v_i_5134_);
lean_inc(v_a_5145_);
v___x_5146_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5145_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; size_t v___x_5149_; size_t v___x_5150_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v___x_5148_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5135_, v_a_5147_);
v___x_5149_ = ((size_t)1ULL);
v___x_5150_ = lean_usize_add(v_i_5134_, v___x_5149_);
v_i_5134_ = v___x_5150_;
v_b_5135_ = v___x_5148_;
goto _start;
}
else
{
lean_dec_ref(v_b_5135_);
return v___x_5146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v_info_5160_; lean_object* v___x_5161_; size_t v_sz_5162_; size_t v___x_5163_; lean_object* v___x_5164_; 
v_info_5160_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5161_ = l_Lean_Parser_Term_getDoElems(v_stx_5152_);
v_sz_5162_ = lean_array_size(v___x_5161_);
v___x_5163_ = ((size_t)0ULL);
v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5161_, v_sz_5162_, v___x_5163_, v_info_5160_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_);
lean_dec_ref(v___x_5161_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
lean_dec(v_a_5169_);
lean_dec_ref(v_a_5168_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_);
lean_dec(v_a_5180_);
lean_dec_ref(v_a_5179_);
lean_dec(v_a_5178_);
lean_dec_ref(v_a_5177_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5183_, lean_object* v_sz_5184_, lean_object* v_i_5185_, lean_object* v_b_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
size_t v_sz_boxed_5194_; size_t v_i_boxed_5195_; lean_object* v_res_5196_; 
v_sz_boxed_5194_ = lean_unbox_usize(v_sz_5184_);
lean_dec(v_sz_5184_);
v_i_boxed_5195_ = lean_unbox_usize(v_i_5185_);
lean_dec(v_i_5185_);
v_res_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5183_, v_sz_boxed_5194_, v_i_boxed_5195_, v_b_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec_ref(v_as_5183_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5197_, lean_object* v_sz_5198_, lean_object* v_i_5199_, lean_object* v_b_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
size_t v_sz_boxed_5208_; size_t v_i_boxed_5209_; lean_object* v_res_5210_; 
v_sz_boxed_5208_ = lean_unbox_usize(v_sz_5198_);
lean_dec(v_sz_5198_);
v_i_boxed_5209_ = lean_unbox_usize(v_i_5199_);
lean_dec(v_i_5199_);
v_res_5210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5197_, v_sz_boxed_5208_, v_i_boxed_5209_, v_b_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec_ref(v_as_5197_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5211_, lean_object* v_rhs_x3f_5212_, lean_object* v_otherwise_x3f_5213_, lean_object* v_body_x3f_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_){
_start:
{
lean_object* v_res_5222_; 
v_res_5222_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5211_, v_rhs_x3f_5212_, v_otherwise_x3f_5213_, v_body_x3f_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_a_5216_);
lean_dec_ref(v_a_5215_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5223_, lean_object* v_as_5224_, lean_object* v_sz_5225_, lean_object* v_i_5226_, lean_object* v_b_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
uint8_t v___x_176499__boxed_5235_; size_t v_sz_boxed_5236_; size_t v_i_boxed_5237_; lean_object* v_res_5238_; 
v___x_176499__boxed_5235_ = lean_unbox(v___x_5223_);
v_sz_boxed_5236_ = lean_unbox_usize(v_sz_5225_);
lean_dec(v_sz_5225_);
v_i_boxed_5237_ = lean_unbox_usize(v_i_5226_);
lean_dec(v_i_5226_);
v_res_5238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_176499__boxed_5235_, v_as_5224_, v_sz_boxed_5236_, v_i_boxed_5237_, v_b_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec_ref(v_as_5224_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5239_, lean_object* v_as_5240_, lean_object* v_sz_5241_, lean_object* v_i_5242_, lean_object* v_b_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
uint8_t v___x_176546__boxed_5251_; size_t v_sz_boxed_5252_; size_t v_i_boxed_5253_; lean_object* v_res_5254_; 
v___x_176546__boxed_5251_ = lean_unbox(v___x_5239_);
v_sz_boxed_5252_ = lean_unbox_usize(v_sz_5241_);
lean_dec(v_sz_5241_);
v_i_boxed_5253_ = lean_unbox_usize(v_i_5242_);
lean_dec(v_i_5242_);
v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_176546__boxed_5251_, v_as_5240_, v_sz_boxed_5252_, v_i_boxed_5253_, v_b_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec_ref(v_as_5240_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5255_, lean_object* v_sz_5256_, lean_object* v_i_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
size_t v_sz_boxed_5266_; size_t v_i_boxed_5267_; lean_object* v_res_5268_; 
v_sz_boxed_5266_ = lean_unbox_usize(v_sz_5256_);
lean_dec(v_sz_5256_);
v_i_boxed_5267_ = lean_unbox_usize(v_i_5257_);
lean_dec(v_i_5257_);
v_res_5268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5255_, v_sz_boxed_5266_, v_i_boxed_5267_, v_b_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec_ref(v_as_5255_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5269_, lean_object* v_decl_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_){
_start:
{
uint8_t v_reassignment_boxed_5278_; lean_object* v_res_5279_; 
v_reassignment_boxed_5278_ = lean_unbox(v_reassignment_5269_);
v_res_5279_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5278_, v_decl_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_);
lean_dec(v_a_5276_);
lean_dec_ref(v_a_5275_);
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5307_, lean_object* v_ref_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5308_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5317_, lean_object* v_ref_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5317_, v_ref_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5327_, lean_object* v_x_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v___x_5336_; 
v___x_5336_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5337_, lean_object* v_x_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_){
_start:
{
lean_object* v_res_5346_; 
v_res_5346_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5337_, v_x_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5347_, lean_object* v_as_5348_, lean_object* v_as_x27_5349_, lean_object* v_b_5350_, lean_object* v_a_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v___x_5359_; 
v___x_5359_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5347_, v_as_x27_5349_, v_b_5350_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5360_, lean_object* v_as_5361_, lean_object* v_as_x27_5362_, lean_object* v_b_5363_, lean_object* v_a_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5360_, v_as_5361_, v_as_x27_5362_, v_b_5363_, v_a_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v_as_x27_5362_);
lean_dec(v_as_5361_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5373_, lean_object* v_msg_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5383_, lean_object* v_msg_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5383_, v_msg_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5393_, lean_object* v_msg_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v___x_5402_; 
v___x_5402_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5393_, v_msg_5394_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5403_, lean_object* v_msg_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5403_, v_msg_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5413_, lean_object* v_as_x27_5414_, lean_object* v_b_5415_, lean_object* v_a_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v___x_5424_; 
v___x_5424_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5414_, v_b_5415_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5425_, lean_object* v_as_x27_5426_, lean_object* v_b_5427_, lean_object* v_a_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5425_, v_as_x27_5426_, v_b_5427_, v_a_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec(v_as_x27_5426_);
lean_dec(v_as_5425_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5437_, lean_object* v_ref_5438_, lean_object* v_msg_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v___x_5447_; 
v___x_5447_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5438_, v_msg_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5448_, lean_object* v_ref_5449_, lean_object* v_msg_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5448_, v_ref_5449_, v_msg_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v_ref_5449_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5459_, lean_object* v_macroStack_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v___x_5468_; 
v___x_5468_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5459_, v_macroStack_5460_, v___y_5465_);
return v___x_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5469_, lean_object* v_macroStack_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_){
_start:
{
lean_object* v_res_5478_; 
v_res_5478_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5469_, v_macroStack_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
lean_dec(v___y_5476_);
lean_dec_ref(v___y_5475_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
return v_res_5478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5479_, lean_object* v_m_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v___x_5482_; 
v___x_5482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5480_, v_a_5481_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5483_, lean_object* v_m_5484_, lean_object* v_a_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5483_, v_m_5484_, v_a_5485_);
lean_dec(v_a_5485_);
lean_dec_ref(v_m_5484_);
return v_res_5486_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5487_, lean_object* v_x_5488_, lean_object* v_x_5489_){
_start:
{
uint8_t v___x_5490_; 
v___x_5490_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5488_, v_x_5489_);
return v___x_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5491_, lean_object* v_x_5492_, lean_object* v_x_5493_){
_start:
{
uint8_t v_res_5494_; lean_object* v_r_5495_; 
v_res_5494_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5491_, v_x_5492_, v_x_5493_);
lean_dec_ref(v_x_5493_);
lean_dec_ref(v_x_5492_);
v_r_5495_ = lean_box(v_res_5494_);
return v_r_5495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27_spec__34(lean_object* v_00_u03b2_5496_){
_start:
{
lean_object* v___x_5497_; 
v___x_5497_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27___redArg(){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27___redArg___boxed(lean_object* v___dummy_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27___redArg();
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__27(lean_object* v_00_u03b2_5502_){
_start:
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30(lean_object* v_00_u03b2_5504_, lean_object* v_a_5505_, lean_object* v_x_5506_){
_start:
{
lean_object* v___x_5507_; 
v___x_5507_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___redArg(v_a_5505_, v_x_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30___boxed(lean_object* v_00_u03b2_5508_, lean_object* v_a_5509_, lean_object* v_x_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__30(v_00_u03b2_5508_, v_a_5509_, v_x_5510_);
lean_dec(v_x_5510_);
lean_dec(v_a_5509_);
return v_res_5511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5512_, lean_object* v_x_5513_, size_t v_x_5514_, lean_object* v_x_5515_){
_start:
{
uint8_t v___x_5516_; 
v___x_5516_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5513_, v_x_5514_, v_x_5515_);
return v___x_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5517_, lean_object* v_x_5518_, lean_object* v_x_5519_, lean_object* v_x_5520_){
_start:
{
size_t v_x_183570__boxed_5521_; uint8_t v_res_5522_; lean_object* v_r_5523_; 
v_x_183570__boxed_5521_ = lean_unbox_usize(v_x_5519_);
lean_dec(v_x_5519_);
v_res_5522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5517_, v_x_5518_, v_x_183570__boxed_5521_, v_x_5520_);
lean_dec_ref(v_x_5520_);
lean_dec_ref(v_x_5518_);
v_r_5523_ = lean_box(v_res_5522_);
return v_r_5523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5524_, lean_object* v_keys_5525_, lean_object* v_vals_5526_, lean_object* v_heq_5527_, lean_object* v_i_5528_, lean_object* v_k_5529_){
_start:
{
uint8_t v___x_5530_; 
v___x_5530_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5525_, v_i_5528_, v_k_5529_);
return v___x_5530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5531_, lean_object* v_keys_5532_, lean_object* v_vals_5533_, lean_object* v_heq_5534_, lean_object* v_i_5535_, lean_object* v_k_5536_){
_start:
{
uint8_t v_res_5537_; lean_object* v_r_5538_; 
v_res_5537_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5531_, v_keys_5532_, v_vals_5533_, v_heq_5534_, v_i_5535_, v_k_5536_);
lean_dec_ref(v_k_5536_);
lean_dec_ref(v_vals_5533_);
lean_dec_ref(v_keys_5532_);
v_r_5538_ = lean_box(v_res_5537_);
return v_r_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_){
_start:
{
lean_object* v___x_5547_; 
v___x_5547_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_);
lean_dec(v_a_5554_);
lean_dec_ref(v_a_5553_);
lean_dec(v_a_5552_);
lean_dec_ref(v_a_5551_);
lean_dec(v_a_5550_);
lean_dec_ref(v_a_5549_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_){
_start:
{
lean_object* v___x_5565_; 
v___x_5565_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_);
return v___x_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
lean_object* v_res_5574_; 
v_res_5574_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
lean_dec(v_a_5572_);
lean_dec_ref(v_a_5571_);
lean_dec(v_a_5570_);
lean_dec_ref(v_a_5569_);
lean_dec(v_a_5568_);
lean_dec_ref(v_a_5567_);
return v_res_5574_;
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
