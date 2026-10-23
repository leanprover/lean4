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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_26_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_29_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_29_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_28_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_27_);
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
v___y_27_ = v___y_38_;
v___y_28_ = v___y_37_;
v___y_29_ = v_numRegularExits_39_;
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
v___y_27_ = v___y_38_;
v___y_28_ = v___y_37_;
v___y_29_ = v_numRegularExits_42_;
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
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
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
uint8_t v___y_57_; lean_object* v___y_58_; uint8_t v___y_59_; uint8_t v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_61_, v___y_62_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_58_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_60_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_57_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_59_);
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
v___y_58_ = v___x_79_;
v___y_59_ = v___y_75_;
v___y_60_ = v___y_74_;
v___y_61_ = v_reassigns_71_;
v___y_62_ = v_reassigns_78_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_73_;
v___y_58_ = v___x_79_;
v___y_59_ = v___y_75_;
v___y_60_ = v___y_74_;
v___y_61_ = v_reassigns_71_;
v___y_62_ = v_reassigns_78_;
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
lean_ctor_set(v___x_140_, 0, v___y_135_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_box(0);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11));
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_144_, v___f_132_, v___x_143_, v___y_136_);
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
v___y_135_ = v___x_169_;
v___y_136_ = v_reassigns_155_;
v___y_137_ = v___x_170_;
goto v___jp_134_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_135_ = v___x_169_;
v___y_136_ = v_reassigns_155_;
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
uint8_t v___x_173404__boxed_526_; uint8_t v___x_173405__boxed_527_; size_t v_i_boxed_528_; size_t v_stop_boxed_529_; lean_object* v_res_530_; 
v___x_173404__boxed_526_ = lean_unbox(v___x_520_);
v___x_173405__boxed_527_ = lean_unbox(v___x_521_);
v_i_boxed_528_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_529_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_173404__boxed_526_, v___x_173405__boxed_527_, v_as_522_, v_i_boxed_528_, v_stop_boxed_529_, v_b_525_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_776_, lean_object* v_x_777_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_785_, v_x_786_);
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
v___x_806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_789_, v___x_805_);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object* v___x_812_, lean_object* v_entry_813_, lean_object* v_s_814_){
_start:
{
lean_object* v_addEntryFn_815_; lean_object* v_importedEntries_816_; lean_object* v_state_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_addEntryFn_815_ = lean_ctor_get(v___x_812_, 3);
lean_inc(v_addEntryFn_815_);
lean_dec_ref(v___x_812_);
v_importedEntries_816_ = lean_ctor_get(v_s_814_, 0);
v_state_817_ = lean_ctor_get(v_s_814_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_s_814_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v_s_814_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_state_817_);
lean_inc(v_importedEntries_816_);
lean_dec(v_s_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_state_821_; lean_object* v___x_823_; 
v_state_821_ = lean_apply_2(v_addEntryFn_815_, v_state_817_, v_entry_813_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_state_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_importedEntries_816_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_state_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_826_, lean_object* v_i_827_, lean_object* v_k_828_){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_array_get_size(v_keys_826_);
v___x_830_ = lean_nat_dec_lt(v_i_827_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec(v_i_827_);
return v___x_830_;
}
else
{
lean_object* v_k_x27_831_; uint8_t v___x_832_; 
v_k_x27_831_ = lean_array_fget_borrowed(v_keys_826_, v_i_827_);
v___x_832_ = l_Lean_instBEqExtraModUse_beq(v_k_828_, v_k_x27_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_i_827_, v___x_833_);
lean_dec(v_i_827_);
v_i_827_ = v___x_834_;
goto _start;
}
else
{
lean_dec(v_i_827_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_836_, v_i_837_, v_k_838_);
lean_dec_ref(v_k_838_);
lean_dec_ref(v_keys_836_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_841_, size_t v_x_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_object* v_es_844_; lean_object* v___x_845_; size_t v___x_846_; size_t v___x_847_; lean_object* v_j_848_; lean_object* v___x_849_; 
v_es_844_ = lean_ctor_get(v_x_841_, 0);
v___x_845_ = lean_box(2);
v___x_846_ = ((size_t)31ULL);
v___x_847_ = lean_usize_land(v_x_842_, v___x_846_);
v_j_848_ = lean_usize_to_nat(v___x_847_);
v___x_849_ = lean_array_get_borrowed(v___x_845_, v_es_844_, v_j_848_);
lean_dec(v_j_848_);
switch(lean_obj_tag(v___x_849_))
{
case 0:
{
lean_object* v_key_850_; uint8_t v___x_851_; 
v_key_850_ = lean_ctor_get(v___x_849_, 0);
v___x_851_ = l_Lean_instBEqExtraModUse_beq(v_x_843_, v_key_850_);
return v___x_851_;
}
case 1:
{
lean_object* v_node_852_; size_t v___x_853_; size_t v___x_854_; 
v_node_852_ = lean_ctor_get(v___x_849_, 0);
v___x_853_ = ((size_t)5ULL);
v___x_854_ = lean_usize_shift_right(v_x_842_, v___x_853_);
v_x_841_ = v_node_852_;
v_x_842_ = v___x_854_;
goto _start;
}
default: 
{
uint8_t v___x_856_; 
v___x_856_ = 0;
return v___x_856_;
}
}
}
else
{
lean_object* v_ks_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_ks_857_ = lean_ctor_get(v_x_841_, 0);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_857_, v___x_858_, v_x_843_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_173932__boxed_863_; uint8_t v_res_864_; lean_object* v_r_865_; 
v_x_173932__boxed_863_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_864_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_860_, v_x_173932__boxed_863_, v_x_862_);
lean_dec_ref(v_x_862_);
lean_dec_ref(v_x_860_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
uint64_t v___x_868_; size_t v___x_869_; uint8_t v___x_870_; 
v___x_868_ = l_Lean_instHashableExtraModUse_hash(v_x_867_);
v___x_869_ = lean_uint64_to_usize(v___x_868_);
v___x_870_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_866_, v___x_869_, v_x_867_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_871_, v_x_872_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_x_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_881_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
lean_ctor_set(v___x_881_, 2, v___x_880_);
lean_ctor_set(v___x_881_, 3, v___x_880_);
lean_ctor_set(v___x_881_, 4, v___x_880_);
lean_ctor_set(v___x_881_, 5, v___x_880_);
lean_ctor_set(v___x_881_, 6, v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_cls_894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_895_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_896_ = l_Lean_Name_append(v___x_895_, v_cls_894_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_907_, uint8_t v_isMeta_908_, lean_object* v_hint_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_env_951_; uint8_t v_isExporting_952_; lean_object* v_entry_953_; lean_object* v___x_954_; lean_object* v_env_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_949_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_950_ = lean_st_ref_get(v___y_915_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
v_isExporting_952_ = lean_ctor_get_uint8(v_env_951_, sizeof(void*)*13);
lean_dec_ref(v_env_951_);
lean_inc(v_mod_907_);
v_entry_953_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_953_, 0, v_mod_907_);
lean_ctor_set_uint8(v_entry_953_, sizeof(void*)*1, v_isExporting_952_);
lean_ctor_set_uint8(v_entry_953_, sizeof(void*)*1 + 1, v_isMeta_908_);
v___x_954_ = lean_st_ref_get(v___y_915_);
v_env_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_ref(v_env_955_);
lean_dec(v___x_954_);
v___x_956_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_957_ = lean_box(1);
v___x_958_ = lean_box(0);
v___x_959_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_949_, v___x_956_, v_env_955_, v___x_957_, v___x_958_);
v___x_960_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_959_, v_entry_953_);
lean_dec(v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v_toCold_961_; lean_object* v_options_962_; lean_object* v_inheritedTraceOptions_963_; uint8_t v_hasTrace_964_; lean_object* v___f_965_; uint8_t v___x_966_; lean_object* v___y_968_; lean_object* v___y_969_; 
v_toCold_961_ = lean_ctor_get(v___y_914_, 0);
v_options_962_ = lean_ctor_get(v_toCold_961_, 2);
v_inheritedTraceOptions_963_ = lean_ctor_get(v_toCold_961_, 11);
v_hasTrace_964_ = lean_ctor_get_uint8(v_options_962_, sizeof(void*)*1);
v___f_965_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0), 3, 2);
lean_closure_set(v___f_965_, 0, v___x_956_);
lean_closure_set(v___f_965_, 1, v_entry_953_);
v___x_966_ = 1;
if (v_hasTrace_964_ == 0)
{
lean_dec(v_hint_909_);
lean_dec(v_mod_907_);
v___y_968_ = v___y_913_;
v___y_969_ = v___y_915_;
goto v___jp_967_;
}
else
{
lean_object* v_cls_996_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_cls_996_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_1016_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_1017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_963_, v_options_962_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_hint_909_);
lean_dec(v_mod_907_);
v___y_968_ = v___y_913_;
v___y_969_ = v___y_915_;
goto v___jp_967_;
}
else
{
lean_object* v___x_1018_; lean_object* v___y_1020_; 
v___x_1018_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_952_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_1020_ = v___x_1027_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_1020_ = v___x_1028_;
goto v___jp_1019_;
}
v___jp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_inc_ref(v___y_1020_);
v___x_1021_ = l_Lean_stringToMessageData(v___y_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1018_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
if (v_isMeta_908_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_1003_ = v___x_1024_;
v___y_1004_ = v___x_1025_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_1003_ = v___x_1024_;
v___y_1004_ = v___x_1026_;
goto v___jp_1002_;
}
}
}
v___jp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___y_998_);
lean_ctor_set(v___x_1000_, 1, v___y_999_);
v___x_1001_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_996_, v___x_1000_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_dec_ref_known(v___x_1001_, 1);
v___y_968_ = v___y_913_;
v___y_969_ = v___y_915_;
goto v___jp_967_;
}
else
{
lean_dec_ref(v___f_965_);
return v___x_1001_;
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
lean_inc_ref(v___y_1004_);
v___x_1005_ = l_Lean_stringToMessageData(v___y_1004_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___y_1003_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_MessageData_ofName(v_mod_907_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_Name_isAnonymous(v_hint_909_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_1013_ = l_Lean_MessageData_ofName(v_hint_909_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___y_998_ = v___x_1010_;
v___y_999_ = v___x_1014_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v_hint_909_);
v___x_1015_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_998_ = v___x_1010_;
v___y_999_ = v___x_1015_;
goto v___jp_997_;
}
}
}
v___jp_967_:
{
lean_object* v___x_970_; lean_object* v_toEnvExtension_971_; uint8_t v_logWrites_972_; 
v___x_970_ = lean_st_ref_take(v___y_969_);
v_toEnvExtension_971_ = lean_ctor_get(v___x_956_, 0);
v_logWrites_972_ = lean_ctor_get_uint8(v_toEnvExtension_971_, sizeof(void*)*6);
if (v_logWrites_972_ == 0)
{
lean_object* v_env_973_; lean_object* v_nextMacroScope_974_; lean_object* v_ngen_975_; lean_object* v_auxDeclNGen_976_; lean_object* v_traceState_977_; lean_object* v_recordedDeps_978_; lean_object* v_messages_979_; lean_object* v_infoState_980_; lean_object* v_snapshotTasks_981_; lean_object* v_asyncMode_982_; lean_object* v___x_983_; 
v_env_973_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_973_);
v_nextMacroScope_974_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_nextMacroScope_974_);
v_ngen_975_ = lean_ctor_get(v___x_970_, 2);
lean_inc_ref(v_ngen_975_);
v_auxDeclNGen_976_ = lean_ctor_get(v___x_970_, 3);
lean_inc_ref(v_auxDeclNGen_976_);
v_traceState_977_ = lean_ctor_get(v___x_970_, 4);
lean_inc_ref(v_traceState_977_);
v_recordedDeps_978_ = lean_ctor_get(v___x_970_, 6);
lean_inc_ref(v_recordedDeps_978_);
v_messages_979_ = lean_ctor_get(v___x_970_, 7);
lean_inc_ref(v_messages_979_);
v_infoState_980_ = lean_ctor_get(v___x_970_, 8);
lean_inc_ref(v_infoState_980_);
v_snapshotTasks_981_ = lean_ctor_get(v___x_970_, 9);
lean_inc_ref(v_snapshotTasks_981_);
lean_dec(v___x_970_);
v_asyncMode_982_ = lean_ctor_get(v_toEnvExtension_971_, 2);
lean_inc_ref(v_toEnvExtension_971_);
v___x_983_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_971_, v_env_973_, v___f_965_, v_asyncMode_982_, v___x_958_, v___x_966_);
v___y_918_ = v_nextMacroScope_974_;
v___y_919_ = v_messages_979_;
v___y_920_ = v___y_969_;
v___y_921_ = v___y_968_;
v___y_922_ = v_recordedDeps_978_;
v___y_923_ = v_traceState_977_;
v___y_924_ = v_auxDeclNGen_976_;
v___y_925_ = v_ngen_975_;
v___y_926_ = v_infoState_980_;
v___y_927_ = v_snapshotTasks_981_;
v___y_928_ = v___x_983_;
goto v___jp_917_;
}
else
{
lean_object* v_env_984_; lean_object* v_nextMacroScope_985_; lean_object* v_ngen_986_; lean_object* v_auxDeclNGen_987_; lean_object* v_traceState_988_; lean_object* v_recordedDeps_989_; lean_object* v_messages_990_; lean_object* v_infoState_991_; lean_object* v_snapshotTasks_992_; lean_object* v_asyncMode_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_env_984_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_984_);
v_nextMacroScope_985_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_nextMacroScope_985_);
v_ngen_986_ = lean_ctor_get(v___x_970_, 2);
lean_inc_ref(v_ngen_986_);
v_auxDeclNGen_987_ = lean_ctor_get(v___x_970_, 3);
lean_inc_ref(v_auxDeclNGen_987_);
v_traceState_988_ = lean_ctor_get(v___x_970_, 4);
lean_inc_ref(v_traceState_988_);
v_recordedDeps_989_ = lean_ctor_get(v___x_970_, 6);
lean_inc_ref(v_recordedDeps_989_);
v_messages_990_ = lean_ctor_get(v___x_970_, 7);
lean_inc_ref(v_messages_990_);
v_infoState_991_ = lean_ctor_get(v___x_970_, 8);
lean_inc_ref(v_infoState_991_);
v_snapshotTasks_992_ = lean_ctor_get(v___x_970_, 9);
lean_inc_ref(v_snapshotTasks_992_);
lean_dec(v___x_970_);
v_asyncMode_993_ = lean_ctor_get(v_toEnvExtension_971_, 2);
lean_inc_ref_n(v_toEnvExtension_971_, 2);
v___x_994_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_971_, v_env_984_);
lean_dec_ref(v_env_984_);
v___x_995_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_971_, v___x_994_, v___f_965_, v_asyncMode_993_, v___x_958_, v___x_966_);
v___y_918_ = v_nextMacroScope_985_;
v___y_919_ = v_messages_990_;
v___y_920_ = v___y_969_;
v___y_921_ = v___y_968_;
v___y_922_ = v_recordedDeps_989_;
v___y_923_ = v_traceState_988_;
v___y_924_ = v_auxDeclNGen_987_;
v___y_925_ = v_ngen_986_;
v___y_926_ = v_infoState_991_;
v___y_927_ = v_snapshotTasks_992_;
v___y_928_ = v___x_995_;
goto v___jp_917_;
}
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref_known(v_entry_953_, 1);
lean_dec(v_hint_909_);
lean_dec(v_mod_907_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
v___jp_917_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_mctx_933_; lean_object* v_zetaDeltaFVarIds_934_; lean_object* v_postponed_935_; lean_object* v_diag_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_947_; 
v___x_929_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_930_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_930_, 0, v___y_928_);
lean_ctor_set(v___x_930_, 1, v___y_918_);
lean_ctor_set(v___x_930_, 2, v___y_925_);
lean_ctor_set(v___x_930_, 3, v___y_924_);
lean_ctor_set(v___x_930_, 4, v___y_923_);
lean_ctor_set(v___x_930_, 5, v___x_929_);
lean_ctor_set(v___x_930_, 6, v___y_922_);
lean_ctor_set(v___x_930_, 7, v___y_919_);
lean_ctor_set(v___x_930_, 8, v___y_926_);
lean_ctor_set(v___x_930_, 9, v___y_927_);
v___x_931_ = lean_st_ref_put(v___y_920_, v___x_930_);
v___x_932_ = lean_st_ref_take(v___y_921_);
v_mctx_933_ = lean_ctor_get(v___x_932_, 0);
v_zetaDeltaFVarIds_934_ = lean_ctor_get(v___x_932_, 2);
v_postponed_935_ = lean_ctor_get(v___x_932_, 3);
v_diag_936_ = lean_ctor_get(v___x_932_, 4);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_932_, 1);
lean_dec(v_unused_948_);
v___x_938_ = v___x_932_;
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_diag_936_);
lean_inc(v_postponed_935_);
lean_inc(v_zetaDeltaFVarIds_934_);
lean_inc(v_mctx_933_);
lean_dec(v___x_932_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_mctx_933_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_zetaDeltaFVarIds_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_postponed_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_diag_936_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_st_ref_put(v___y_921_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_940_);
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1031_, lean_object* v_isMeta_1032_, lean_object* v_hint_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v_isMeta_boxed_1041_; lean_object* v_res_1042_; 
v_isMeta_boxed_1041_ = lean_unbox(v_isMeta_1032_);
v_res_1042_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1031_, v_isMeta_boxed_1041_, v_hint_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1043_, lean_object* v_declName_1044_, lean_object* v_as_1045_, size_t v_sz_1046_, size_t v_i_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_usize_dec_lt(v_i_1047_, v_sz_1046_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_declName_1044_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_b_1048_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v_modules_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v_toImport_1063_; lean_object* v_module_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1058_ = l_Lean_Environment_header(v___x_1043_);
v_modules_1059_ = lean_ctor_get(v___x_1058_, 3);
lean_inc_ref(v_modules_1059_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1061_ = lean_array_uget_borrowed(v_as_1045_, v_i_1047_);
v___x_1062_ = lean_array_get(v___x_1060_, v_modules_1059_, v_a_1061_);
lean_dec_ref(v_modules_1059_);
v_toImport_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_toImport_1063_);
lean_dec(v___x_1062_);
v_module_1064_ = lean_ctor_get(v_toImport_1063_, 0);
lean_inc(v_module_1064_);
lean_dec_ref(v_toImport_1063_);
v___x_1065_ = lean_box(0);
v___x_1066_ = 0;
lean_inc(v_declName_1044_);
v___x_1067_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1064_, v___x_1066_, v_declName_1044_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1067_) == 0)
{
size_t v___x_1068_; size_t v___x_1069_; 
lean_dec_ref_known(v___x_1067_, 1);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1047_, v___x_1068_);
v_i_1047_ = v___x_1069_;
v_b_1048_ = v___x_1065_;
goto _start;
}
else
{
lean_dec(v_declName_1044_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1071_, lean_object* v_declName_1072_, lean_object* v_as_1073_, lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1071_, v_declName_1072_, v_as_1073_, v_sz_boxed_1084_, v_i_boxed_1085_, v_b_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v_as_1073_);
lean_dec_ref(v___x_1071_);
return v_res_1086_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1090_, uint8_t v_isMeta_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_env_1104_; lean_object* v___y_1106_; lean_object* v___x_1119_; 
v___x_1099_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1100_ = lean_st_ref_get(v___y_1097_);
v_env_1104_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1104_);
lean_dec(v___x_1100_);
v___x_1119_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1104_, v_declName_1090_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref(v_env_1104_);
lean_dec(v_declName_1090_);
goto v___jp_1101_;
}
else
{
lean_object* v_val_1120_; lean_object* v___x_1121_; lean_object* v_modules_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_val_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_val_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Environment_header(v_env_1104_);
v_modules_1122_ = lean_ctor_get(v___x_1121_, 3);
lean_inc_ref(v_modules_1122_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = lean_array_get_size(v_modules_1122_);
v___x_1124_ = lean_nat_dec_lt(v_val_1120_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_modules_1122_);
lean_dec(v_val_1120_);
lean_dec_ref(v_env_1104_);
lean_dec(v_declName_1090_);
goto v___jp_1101_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___y_1128_; 
v___x_1125_ = lean_array_fget(v_modules_1122_, v_val_1120_);
lean_dec(v_val_1120_);
lean_dec_ref(v_modules_1122_);
v___x_1126_ = lean_st_ref_get(v___y_1097_);
if (v_isMeta_1091_ == 0)
{
lean_dec(v___x_1126_);
v___y_1128_ = v_isMeta_1091_;
goto v___jp_1127_;
}
else
{
lean_object* v_env_1139_; uint8_t v___x_1140_; 
v_env_1139_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_env_1139_);
lean_dec(v___x_1126_);
lean_inc(v_declName_1090_);
v___x_1140_ = l_Lean_isMarkedMeta(v_env_1139_, v_declName_1090_);
if (v___x_1140_ == 0)
{
v___y_1128_ = v_isMeta_1091_;
goto v___jp_1127_;
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = 0;
v___y_1128_ = v___x_1141_;
goto v___jp_1127_;
}
}
v___jp_1127_:
{
lean_object* v_toImport_1129_; lean_object* v_module_1130_; lean_object* v___x_1131_; 
v_toImport_1129_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_toImport_1129_);
lean_dec(v___x_1125_);
v_module_1130_ = lean_ctor_get(v_toImport_1129_, 0);
lean_inc(v_module_1130_);
lean_dec_ref(v_toImport_1129_);
lean_inc(v_declName_1090_);
v___x_1131_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1130_, v___y_1128_, v_declName_1090_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = l_Lean_indirectModUseExt;
v___x_1133_ = lean_box(1);
v___x_1134_ = lean_box(0);
lean_inc_ref(v_env_1104_);
v___x_1135_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1099_, v___x_1132_, v_env_1104_, v___x_1133_, v___x_1134_);
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1135_, v_declName_1090_);
lean_dec(v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1106_ = v___x_1137_;
goto v___jp_1105_;
}
else
{
lean_object* v_val_1138_; 
v_val_1138_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v___x_1136_, 1);
v___y_1106_ = v_val_1138_;
goto v___jp_1105_;
}
}
else
{
lean_dec_ref(v_env_1104_);
lean_dec(v_declName_1090_);
return v___x_1131_;
}
}
}
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
v___jp_1105_:
{
lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_box(0);
v_sz_1108_ = lean_array_size(v___y_1106_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1104_, v_declName_1090_, v___y_1106_, v_sz_1108_, v___x_1109_, v___x_1107_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_env_1104_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1110_, 0);
lean_dec(v_unused_1118_);
v___x_1112_ = v___x_1110_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v___x_1110_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1107_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1107_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
return v___x_1110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1142_, lean_object* v_isMeta_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_isMeta_boxed_1151_; lean_object* v_res_1152_; 
v_isMeta_boxed_1151_ = lean_unbox(v_isMeta_1143_);
v_res_1152_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1142_, v_isMeta_boxed_1151_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
if (lean_obj_tag(v_as_x27_1153_) == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1154_);
return v___x_1162_;
}
else
{
lean_object* v_head_1163_; lean_object* v_tail_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; 
v_head_1163_ = lean_ctor_get(v_as_x27_1153_, 0);
v_tail_1164_ = lean_ctor_get(v_as_x27_1153_, 1);
v___x_1165_ = lean_box(0);
v___x_1166_ = 1;
lean_inc(v_head_1163_);
v___x_1167_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1163_, v___x_1166_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_dec_ref_known(v___x_1167_, 1);
v_as_x27_1153_ = v_tail_1164_;
v_b_1154_ = v___x_1165_;
goto _start;
}
else
{
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1169_, v_b_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v_as_x27_1169_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_currNamespace_1179_);
lean_ctor_set(v___x_1182_, 1, v___y_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1187_, lean_object* v___x_1188_, lean_object* v_currNamespace_1189_, lean_object* v_openDecls_1190_, lean_object* v_n_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = l_Lean_ResolveName_resolveGlobalName(v_env_1187_, v___x_1188_, v_currNamespace_1189_, v_openDecls_1190_, v_n_1191_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1196_, lean_object* v___x_1197_, lean_object* v_currNamespace_1198_, lean_object* v_openDecls_1199_, lean_object* v_n_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1196_, v___x_1197_, v_currNamespace_1198_, v_openDecls_1199_, v_n_1200_, v___y_1201_, v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v___x_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1204_, lean_object* v_currNamespace_1205_, lean_object* v_openDecls_1206_, lean_object* v_n_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = l_Lean_ResolveName_resolveNamespace(v_env_1204_, v_currNamespace_1205_, v_openDecls_1206_, v_n_1207_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1212_, lean_object* v_currNamespace_1213_, lean_object* v_openDecls_1214_, lean_object* v_n_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1212_, v_currNamespace_1213_, v_openDecls_1214_, v_n_1215_, v___y_1216_, v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v_toCold_1229_; lean_object* v_env_1230_; lean_object* v_currRecDepth_1231_; lean_object* v_ref_1232_; lean_object* v_maxRecDepth_1233_; lean_object* v_currNamespace_1234_; lean_object* v_openDecls_1235_; lean_object* v_quotContext_1236_; lean_object* v_currMacroScope_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v_methods_1244_; lean_object* v___x_1245_; lean_object* v_nextMacroScope_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1228_ = lean_st_ref_get(v___y_1226_);
v_toCold_1229_ = lean_ctor_get(v___y_1225_, 0);
v_env_1230_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_ref_n(v_env_1230_, 4);
lean_dec(v___x_1228_);
v_currRecDepth_1231_ = lean_ctor_get(v___y_1225_, 1);
v_ref_1232_ = lean_ctor_get(v___y_1225_, 2);
v_maxRecDepth_1233_ = lean_ctor_get(v_toCold_1229_, 3);
v_currNamespace_1234_ = lean_ctor_get(v_toCold_1229_, 4);
v_openDecls_1235_ = lean_ctor_get(v_toCold_1229_, 5);
v_quotContext_1236_ = lean_ctor_get(v_toCold_1229_, 8);
v_currMacroScope_1237_ = lean_ctor_get(v_toCold_1229_, 9);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1238_, 0, v_env_1230_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1239_, 0, v_env_1230_);
v___x_1240_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1225_);
lean_inc_n(v_currNamespace_1234_, 3);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1241_, 0, v_currNamespace_1234_);
lean_inc_n(v_openDecls_1235_, 2);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1242_, 0, v_env_1230_);
lean_closure_set(v___f_1242_, 1, v___x_1240_);
lean_closure_set(v___f_1242_, 2, v_currNamespace_1234_);
lean_closure_set(v___f_1242_, 3, v_openDecls_1235_);
v___f_1243_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1243_, 0, v_env_1230_);
lean_closure_set(v___f_1243_, 1, v_currNamespace_1234_);
lean_closure_set(v___f_1243_, 2, v_openDecls_1235_);
v_methods_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1244_, 0, v___f_1239_);
lean_ctor_set(v_methods_1244_, 1, v___f_1241_);
lean_ctor_set(v_methods_1244_, 2, v___f_1238_);
lean_ctor_set(v_methods_1244_, 3, v___f_1243_);
lean_ctor_set(v_methods_1244_, 4, v___f_1242_);
v___x_1245_ = lean_st_ref_get(v___y_1226_);
v_nextMacroScope_1246_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_nextMacroScope_1246_);
lean_dec(v___x_1245_);
lean_inc(v_ref_1232_);
lean_inc(v_maxRecDepth_1233_);
lean_inc(v_currRecDepth_1231_);
lean_inc(v_currMacroScope_1237_);
lean_inc(v_quotContext_1236_);
v___x_1247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1247_, 0, v_methods_1244_);
lean_ctor_set(v___x_1247_, 1, v_quotContext_1236_);
lean_ctor_set(v___x_1247_, 2, v_currMacroScope_1237_);
lean_ctor_set(v___x_1247_, 3, v_currRecDepth_1231_);
lean_ctor_set(v___x_1247_, 4, v_maxRecDepth_1233_);
lean_ctor_set(v___x_1247_, 5, v_ref_1232_);
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v_nextMacroScope_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
v___x_1250_ = lean_apply_2(v_x_1220_, v___x_1247_, v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_a_1252_; lean_object* v_macroScope_1253_; lean_object* v_traceMsgs_1254_; lean_object* v_expandedMacroDecls_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_a_1251_);
v_a_1252_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1250_, 2);
v_macroScope_1253_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_macroScope_1253_);
v_traceMsgs_1254_ = lean_ctor_get(v_a_1251_, 1);
lean_inc(v_traceMsgs_1254_);
v_expandedMacroDecls_1255_ = lean_ctor_get(v_a_1251_, 2);
lean_inc(v_expandedMacroDecls_1255_);
lean_dec(v_a_1251_);
v___x_1256_ = lean_box(0);
v___x_1257_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1255_, v___x_1256_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v_expandedMacroDecls_1255_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v_env_1259_; lean_object* v_ngen_1260_; lean_object* v_auxDeclNGen_1261_; lean_object* v_traceState_1262_; lean_object* v_cache_1263_; lean_object* v_recordedDeps_1264_; lean_object* v_messages_1265_; lean_object* v_infoState_1266_; lean_object* v_snapshotTasks_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref_known(v___x_1257_, 1);
v___x_1258_ = lean_st_ref_take(v___y_1226_);
v_env_1259_ = lean_ctor_get(v___x_1258_, 0);
v_ngen_1260_ = lean_ctor_get(v___x_1258_, 2);
v_auxDeclNGen_1261_ = lean_ctor_get(v___x_1258_, 3);
v_traceState_1262_ = lean_ctor_get(v___x_1258_, 4);
v_cache_1263_ = lean_ctor_get(v___x_1258_, 5);
v_recordedDeps_1264_ = lean_ctor_get(v___x_1258_, 6);
v_messages_1265_ = lean_ctor_get(v___x_1258_, 7);
v_infoState_1266_ = lean_ctor_get(v___x_1258_, 8);
v_snapshotTasks_1267_ = lean_ctor_get(v___x_1258_, 9);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1258_, 1);
lean_dec(v_unused_1294_);
v___x_1269_ = v___x_1258_;
v_isShared_1270_ = v_isSharedCheck_1293_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_snapshotTasks_1267_);
lean_inc(v_infoState_1266_);
lean_inc(v_messages_1265_);
lean_inc(v_recordedDeps_1264_);
lean_inc(v_cache_1263_);
lean_inc(v_traceState_1262_);
lean_inc(v_auxDeclNGen_1261_);
lean_inc(v_ngen_1260_);
lean_inc(v_env_1259_);
lean_dec(v___x_1258_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1293_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_macroScope_1253_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_env_1259_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_macroScope_1253_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_ngen_1260_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_auxDeclNGen_1261_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_traceState_1262_);
lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_cache_1263_);
lean_ctor_set(v_reuseFailAlloc_1292_, 6, v_recordedDeps_1264_);
lean_ctor_set(v_reuseFailAlloc_1292_, 7, v_messages_1265_);
lean_ctor_set(v_reuseFailAlloc_1292_, 8, v_infoState_1266_);
lean_ctor_set(v_reuseFailAlloc_1292_, 9, v_snapshotTasks_1267_);
v___x_1272_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_st_ref_put(v___y_1226_, v___x_1272_);
v___x_1274_ = l_List_reverse___redArg(v_traceMsgs_1254_);
v___x_1275_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1274_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1283_);
v___x_1277_ = v___x_1275_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v___x_1275_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_a_1252_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1252_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_a_1252_);
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1275_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_traceMsgs_1254_);
lean_dec(v_macroScope_1253_);
lean_dec(v_a_1252_);
v_a_1295_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1257_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1257_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; 
v_a_1303_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1250_, 2);
if (lean_obj_tag(v_a_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_a_1304_ = lean_ctor_get(v_a_1303_, 0);
lean_inc(v_a_1304_);
v_a_1305_ = lean_ctor_get(v_a_1303_, 1);
lean_inc_ref(v_a_1305_);
lean_dec_ref_known(v_a_1303_, 2);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1307_ = lean_string_dec_eq(v_a_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1305_);
v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
v___x_1310_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1304_, v___x_1309_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v_a_1304_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_a_1305_);
v___x_1311_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1304_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1325_, size_t v_i_1326_, lean_object* v_bs_1327_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_lt(v_i_1326_, v_sz_1325_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_bs_1327_);
return v___x_1329_;
}
else
{
lean_object* v_v_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_v_1330_ = lean_array_uget(v_bs_1327_, v_i_1326_);
v___x_1331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1330_);
v___x_1332_ = l_Lean_Syntax_isOfKind(v_v_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v_v_1330_);
lean_dec_ref(v_bs_1327_);
v___x_1333_ = lean_box(0);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_Syntax_getArg(v_v_1330_, v___x_1334_);
v___x_1336_ = l_Lean_Syntax_isOfKind(v___x_1335_, v___x_1331_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v_v_1330_);
lean_dec_ref(v_bs_1327_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; lean_object* v_bs_x27_1339_; lean_object* v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_unsigned_to_nat(3u);
v_bs_x27_1339_ = lean_array_uset(v_bs_1327_, v_i_1326_, v___x_1334_);
v___x_1340_ = l_Lean_Syntax_getArg(v_v_1330_, v___x_1338_);
lean_dec(v_v_1330_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1326_, v___x_1341_);
v___x_1343_ = lean_array_uset(v_bs_x27_1339_, v_i_1326_, v___x_1340_);
v_i_1326_ = v___x_1342_;
v_bs_1327_ = v___x_1343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_bs_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1348_, v_i_boxed_1349_, v_bs_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_bs_1365_);
return v___x_1367_;
}
else
{
lean_object* v_v_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_v_1368_ = lean_array_uget(v_bs_1365_, v_i_1364_);
v___x_1369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1368_);
v___x_1370_ = l_Lean_Syntax_isOfKind(v_v_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_v_1368_);
lean_dec_ref(v_bs_1365_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = l_Lean_Syntax_getArg(v_v_1368_, v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1375_ = l_Lean_Syntax_isOfKind(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v_v_1368_);
lean_dec_ref(v_bs_1365_);
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_bs_x27_1379_; lean_object* v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1377_ = lean_unsigned_to_nat(3u);
v___x_1378_ = lean_unsigned_to_nat(0u);
v_bs_x27_1379_ = lean_array_uset(v_bs_1365_, v_i_1364_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_getArg(v_v_1368_, v___x_1377_);
lean_dec(v_v_1368_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1364_, v___x_1381_);
v___x_1383_ = lean_array_uset(v_bs_x27_1379_, v_i_1364_, v___x_1380_);
v_i_1364_ = v___x_1382_;
v_bs_1365_ = v___x_1383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_bs_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1388_, v_i_boxed_1389_, v_bs_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1397_, size_t v_i_1398_, lean_object* v_bs_1399_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_usize_dec_lt(v_i_1398_, v_sz_1397_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_bs_1399_);
return v___x_1401_;
}
else
{
lean_object* v_v_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_v_1402_ = lean_array_uget(v_bs_1399_, v_i_1398_);
v___x_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1402_);
v___x_1404_ = l_Lean_Syntax_isOfKind(v_v_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_dec(v_v_1402_);
lean_dec_ref(v_bs_1399_);
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v_bs_x27_1407_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v_bs_x27_1407_ = lean_array_uset(v_bs_1399_, v_i_1398_, v___x_1406_);
v___x_1414_ = l_Lean_Syntax_getArg(v_v_1402_, v___x_1406_);
lean_dec(v_v_1402_);
v___x_1415_ = l_Lean_Syntax_isNone(v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = lean_unsigned_to_nat(2u);
v___x_1417_ = l_Lean_Syntax_matchesNull(v___x_1414_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_bs_x27_1407_);
v___x_1418_ = lean_box(0);
return v___x_1418_;
}
else
{
goto v___jp_1408_;
}
}
else
{
lean_dec(v___x_1414_);
goto v___jp_1408_;
}
v___jp_1408_:
{
lean_object* v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1398_, v___x_1410_);
v___x_1412_ = lean_array_uset(v_bs_x27_1407_, v_i_1398_, v___x_1409_);
v_i_1398_ = v___x_1411_;
v_bs_1399_ = v___x_1412_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_){
_start:
{
size_t v_sz_boxed_1422_; size_t v_i_boxed_1423_; lean_object* v_res_1424_; 
v_sz_boxed_1422_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1423_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1422_, v_i_boxed_1423_, v_bs_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1425_, size_t v_i_1426_, lean_object* v_bs_1427_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_lt(v_i_1426_, v_sz_1425_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_bs_1427_);
return v___x_1429_;
}
else
{
lean_object* v_v_1430_; lean_object* v___x_1431_; lean_object* v_bs_x27_1432_; size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_v_1430_ = lean_array_uget(v_bs_1427_, v_i_1426_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v_bs_x27_1432_ = lean_array_uset(v_bs_1427_, v_i_1426_, v___x_1431_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1426_, v___x_1433_);
v___x_1435_ = lean_array_uset(v_bs_x27_1432_, v_i_1426_, v_v_1430_);
v_i_1426_ = v___x_1434_;
v_bs_1427_ = v___x_1435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1437_, lean_object* v_i_1438_, lean_object* v_bs_1439_){
_start:
{
size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1440_, v_i_boxed_1441_, v_bs_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1444_, v___y_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1448_, v_x_1449_, v___y_1450_, v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v_x_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1456_, lean_object* v_as_x27_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
if (lean_obj_tag(v_as_x27_1457_) == 0)
{
lean_object* v___x_1466_; 
lean_dec(v_stx_1456_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_b_1458_);
return v___x_1466_;
}
else
{
lean_object* v_head_1467_; lean_object* v_tail_1468_; lean_object* v_value_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_b_1458_);
v_head_1467_ = lean_ctor_get(v_as_x27_1457_, 0);
v_tail_1468_ = lean_ctor_get(v_as_x27_1457_, 1);
v_value_1469_ = lean_ctor_get(v_head_1467_, 1);
v___x_1470_ = lean_box(0);
v___x_1471_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1472_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1469_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v_stx_1456_);
v___x_1473_ = lean_apply_8(v_value_1469_, v_stx_1456_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, lean_box(0));
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_stx_1456_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_a_1474_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1470_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1479_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1505_; 
v_a_1484_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1486_ = v___x_1473_;
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1473_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Exception_isInterrupt(v_a_1484_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; 
lean_inc(v_a_1484_);
v___x_1489_ = l_Lean_Exception_isRuntime(v_a_1484_);
if (v___x_1489_ == 0)
{
if (lean_obj_tag(v_a_1484_) == 0)
{
lean_object* v___x_1491_; 
lean_dec(v_stx_1456_);
if (v_isShared_1487_ == 0)
{
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1484_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
else
{
lean_object* v_id_1493_; uint8_t v___x_1494_; 
v_id_1493_ = lean_ctor_get(v_a_1484_, 0);
v___x_1494_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1472_, v_id_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1496_; 
lean_dec(v_stx_1456_);
if (v_isShared_1487_ == 0)
{
v___x_1496_ = v___x_1486_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1484_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
lean_dec_ref_known(v_a_1484_, 2);
lean_del_object(v___x_1486_);
v_as_x27_1457_ = v_tail_1468_;
v_b_1458_ = v___x_1471_;
goto _start;
}
}
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_stx_1456_);
if (v_isShared_1487_ == 0)
{
v___x_1500_ = v___x_1486_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1484_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_stx_1456_);
if (v_isShared_1487_ == 0)
{
v___x_1503_ = v___x_1486_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1484_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1506_, lean_object* v_as_x27_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1506_, v_as_x27_1507_, v_b_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_as_x27_1507_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1519_, lean_object* v_rhs_x3f_1520_, lean_object* v_otherwise_x3f_1521_, lean_object* v_body_x3f_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
uint8_t v___y_1531_; uint8_t v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1534_; uint8_t v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_body_1542_; lean_object* v___y_1560_; lean_object* v_otherwise_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v_rhs_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; 
if (lean_obj_tag(v_rhs_x3f_1520_) == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1573_ = v___x_1584_;
v___y_1574_ = v_a_1523_;
v___y_1575_ = v_a_1524_;
v___y_1576_ = v_a_1525_;
v___y_1577_ = v_a_1526_;
v___y_1578_ = v_a_1527_;
v___y_1579_ = v_a_1528_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1586_; 
v_val_1585_ = lean_ctor_get(v_rhs_x3f_1520_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_rhs_x3f_1520_, 1);
v___x_1586_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1585_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v_rhs_1573_ = v_a_1587_;
v___y_1574_ = v_a_1523_;
v___y_1575_ = v_a_1524_;
v___y_1576_ = v_a_1525_;
v___y_1577_ = v_a_1526_;
v___y_1578_ = v_a_1527_;
v___y_1579_ = v_a_1528_;
goto v___jp_1572_;
}
else
{
lean_dec(v_body_x3f_1522_);
lean_dec(v_otherwise_x3f_1521_);
lean_dec_ref(v_reassigned_1519_);
return v___x_1586_;
}
}
v___jp_1530_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1537_, 0, v___y_1534_);
lean_ctor_set(v___x_1537_, 1, v___y_1536_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2, v___y_1531_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2 + 1, v___y_1535_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2 + 2, v___y_1532_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2 + 3, v___y_1533_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
v___jp_1539_:
{
lean_object* v___x_1543_; lean_object* v_info_1544_; uint8_t v_breaks_1545_; uint8_t v_continues_1546_; uint8_t v_returnsEarly_1547_; lean_object* v_numRegularExits_1548_; uint8_t v_noFallthrough_1549_; lean_object* v_reassigns_1550_; size_t v_sz_1551_; size_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1543_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1542_, v___y_1541_);
v_info_1544_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1540_, v___x_1543_);
v_breaks_1545_ = lean_ctor_get_uint8(v_info_1544_, sizeof(void*)*2);
v_continues_1546_ = lean_ctor_get_uint8(v_info_1544_, sizeof(void*)*2 + 1);
v_returnsEarly_1547_ = lean_ctor_get_uint8(v_info_1544_, sizeof(void*)*2 + 2);
v_numRegularExits_1548_ = lean_ctor_get(v_info_1544_, 0);
lean_inc(v_numRegularExits_1548_);
v_noFallthrough_1549_ = lean_ctor_get_uint8(v_info_1544_, sizeof(void*)*2 + 3);
v_reassigns_1550_ = lean_ctor_get(v_info_1544_, 1);
lean_inc(v_reassigns_1550_);
lean_dec_ref(v_info_1544_);
v_sz_1551_ = lean_array_size(v_reassigned_1519_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1551_, v___x_1552_, v_reassigned_1519_);
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_array_get_size(v___x_1553_);
v___x_1556_ = lean_nat_dec_lt(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v___x_1553_);
v___y_1531_ = v_breaks_1545_;
v___y_1532_ = v_returnsEarly_1547_;
v___y_1533_ = v_noFallthrough_1549_;
v___y_1534_ = v_numRegularExits_1548_;
v___y_1535_ = v_continues_1546_;
v___y_1536_ = v_reassigns_1550_;
goto v___jp_1530_;
}
else
{
size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_usize_of_nat(v___x_1555_);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1553_, v___x_1552_, v___x_1557_, v_reassigns_1550_);
lean_dec_ref(v___x_1553_);
v___y_1531_ = v_breaks_1545_;
v___y_1532_ = v_returnsEarly_1547_;
v___y_1533_ = v_noFallthrough_1549_;
v___y_1534_ = v_numRegularExits_1548_;
v___y_1535_ = v_continues_1546_;
v___y_1536_ = v___x_1558_;
goto v___jp_1530_;
}
}
v___jp_1559_:
{
if (lean_obj_tag(v_body_x3f_1522_) == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1540_ = v___y_1560_;
v___y_1541_ = v_otherwise_1561_;
v_body_1542_ = v___x_1568_;
goto v___jp_1539_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1570_; 
v_val_1569_ = lean_ctor_get(v_body_x3f_1522_, 0);
lean_inc(v_val_1569_);
lean_dec_ref_known(v_body_x3f_1522_, 1);
v___x_1570_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1569_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___y_1540_ = v___y_1560_;
v___y_1541_ = v_otherwise_1561_;
v_body_1542_ = v_a_1571_;
goto v___jp_1539_;
}
else
{
lean_dec_ref(v_otherwise_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_reassigned_1519_);
return v___x_1570_;
}
}
}
v___jp_1572_:
{
if (lean_obj_tag(v_otherwise_x3f_1521_) == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1560_ = v_rhs_1573_;
v_otherwise_1561_ = v___x_1580_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1577_;
v___y_1566_ = v___y_1578_;
v___y_1567_ = v___y_1579_;
goto v___jp_1559_;
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1582_; 
v_val_1581_ = lean_ctor_get(v_otherwise_x3f_1521_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_otherwise_x3f_1521_, 1);
v___x_1582_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1581_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___y_1560_ = v_rhs_1573_;
v_otherwise_1561_ = v_a_1583_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1577_;
v___y_1566_ = v___y_1578_;
v___y_1567_ = v___y_1579_;
goto v___jp_1559_;
}
else
{
lean_dec_ref(v_rhs_1573_);
lean_dec(v_body_x3f_1522_);
lean_dec_ref(v_reassigned_1519_);
return v___x_1582_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1690_, lean_object* v_decl_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v_reassigns_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1691_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_decl_1691_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1691_);
v___x_1730_ = l_Lean_Syntax_isOfKind(v_decl_1691_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1731_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1732_ = lean_box(0);
v___x_1733_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1732_, v___x_1730_);
v___x_1734_ = l_Std_Format_defWidth;
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = l_Std_Format_pretty(v___x_1733_, v___x_1734_, v___x_1735_, v___x_1735_);
v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1731_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1738_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v_pattern_1741_; lean_object* v___y_1743_; lean_object* v_otherwise_x3f_1744_; lean_object* v_body_x3f_x3f_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v_body_x3f_x3f_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___x_1775_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1740_ = lean_unsigned_to_nat(0u);
v_pattern_1741_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1740_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1814_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1775_);
v___x_1815_ = l_Lean_Syntax_isNone(v___x_1814_);
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; 
lean_inc(v___x_1814_);
v___x_1816_ = l_Lean_Syntax_matchesNull(v___x_1814_, v___x_1775_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___x_1814_);
lean_dec(v_pattern_1741_);
v___x_1817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1818_, v___x_1816_);
v___x_1820_ = l_Std_Format_defWidth;
v___x_1821_ = l_Std_Format_pretty(v___x_1819_, v___x_1820_, v___x_1740_, v___x_1740_);
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1817_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1823_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = l_Lean_Syntax_getArg(v___x_1814_, v___x_1740_);
lean_dec(v___x_1814_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1827_ = l_Lean_Syntax_isOfKind(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec(v_pattern_1741_);
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1829_, v___x_1827_);
v___x_1831_ = l_Std_Format_defWidth;
v___x_1832_ = l_Std_Format_pretty(v___x_1830_, v___x_1831_, v___x_1740_, v___x_1740_);
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1828_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1834_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1835_;
}
else
{
v___y_1777_ = v_a_1692_;
v___y_1778_ = v_a_1693_;
v___y_1779_ = v_a_1694_;
v___y_1780_ = v_a_1695_;
v___y_1781_ = v_a_1696_;
v___y_1782_ = v_a_1697_;
goto v___jp_1776_;
}
}
}
else
{
lean_dec(v___x_1814_);
v___y_1777_ = v_a_1692_;
v___y_1778_ = v_a_1693_;
v___y_1779_ = v_a_1694_;
v___y_1780_ = v_a_1695_;
v___y_1781_ = v_a_1696_;
v___y_1782_ = v_a_1697_;
goto v___jp_1776_;
}
v___jp_1742_:
{
if (v_reassignment_1690_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_pattern_1741_);
v___x_1752_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1712_ = v_otherwise_x3f_1744_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v_body_x3f_x3f_1745_;
v_reassigns_1715_ = v___x_1752_;
v___y_1716_ = v___y_1746_;
v___y_1717_ = v___y_1747_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v___y_1749_;
v___y_1720_ = v___y_1750_;
v___y_1721_ = v___y_1751_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1741_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___y_1712_ = v_otherwise_x3f_1744_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v_body_x3f_x3f_1745_;
v_reassigns_1715_ = v_a_1754_;
v___y_1716_ = v___y_1746_;
v___y_1717_ = v___y_1747_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v___y_1749_;
v___y_1720_ = v___y_1750_;
v___y_1721_ = v___y_1751_;
goto v___jp_1711_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_body_x3f_x3f_1745_);
lean_dec(v_otherwise_x3f_1744_);
lean_dec(v___y_1743_);
v_a_1755_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1753_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
v___jp_1763_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___y_1764_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_body_x3f_x3f_1766_);
v___y_1743_ = v___y_1765_;
v_otherwise_x3f_1744_ = v___x_1773_;
v_body_x3f_x3f_1745_ = v___x_1774_;
v___y_1746_ = v___y_1767_;
v___y_1747_ = v___y_1768_;
v___y_1748_ = v___y_1769_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___y_1771_;
v___y_1751_ = v___y_1772_;
goto v___jp_1742_;
}
v___jp_1776_:
{
lean_object* v___x_1783_; lean_object* v_rhs_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1783_ = lean_unsigned_to_nat(3u);
v_rhs_1784_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(4u);
v___x_1786_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1785_);
v___x_1787_ = l_Lean_Syntax_isNone(v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
lean_inc(v___x_1786_);
v___x_1788_ = l_Lean_Syntax_matchesNull(v___x_1786_, v___x_1783_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1786_);
lean_dec(v_rhs_1784_);
lean_dec(v_pattern_1741_);
v___x_1789_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1790_ = lean_box(0);
v___x_1791_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1790_, v___x_1788_);
v___x_1792_ = l_Std_Format_defWidth;
v___x_1793_ = l_Std_Format_pretty(v___x_1791_, v___x_1792_, v___x_1740_, v___x_1740_);
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1789_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1795_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v_otherwise_x3f_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1797_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1798_ = l_Lean_Syntax_getArg(v___x_1786_, v___x_1775_);
v___x_1799_ = l_Lean_Syntax_getArg(v___x_1786_, v___x_1797_);
lean_dec(v___x_1786_);
v___x_1800_ = l_Lean_Syntax_isNone(v___x_1799_);
if (v___x_1800_ == 0)
{
uint8_t v___x_1801_; 
lean_inc(v___x_1799_);
v___x_1801_ = l_Lean_Syntax_matchesNull(v___x_1799_, v___x_1775_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1799_);
lean_dec(v_otherwise_x3f_1798_);
lean_dec(v_rhs_1784_);
lean_dec(v_pattern_1741_);
v___x_1802_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1803_ = lean_box(0);
v___x_1804_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1803_, v___x_1801_);
v___x_1805_ = l_Std_Format_defWidth;
v___x_1806_ = l_Std_Format_pretty(v___x_1804_, v___x_1805_, v___x_1740_, v___x_1740_);
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1808_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1809_;
}
else
{
lean_object* v_body_x3f_x3f_1810_; lean_object* v___x_1811_; 
lean_dec(v_decl_1691_);
v_body_x3f_x3f_1810_ = l_Lean_Syntax_getArg(v___x_1799_, v___x_1740_);
lean_dec(v___x_1799_);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_body_x3f_x3f_1810_);
v___y_1764_ = v_otherwise_x3f_1798_;
v___y_1765_ = v_rhs_1784_;
v_body_x3f_x3f_1766_ = v___x_1811_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1778_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1781_;
v___y_1772_ = v___y_1782_;
goto v___jp_1763_;
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v___x_1799_);
lean_dec(v_decl_1691_);
v___x_1812_ = lean_box(0);
v___y_1764_ = v_otherwise_x3f_1798_;
v___y_1765_ = v_rhs_1784_;
v_body_x3f_x3f_1766_ = v___x_1812_;
v___y_1767_ = v___y_1777_;
v___y_1768_ = v___y_1778_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1781_;
v___y_1772_ = v___y_1782_;
goto v___jp_1763_;
}
}
}
else
{
lean_object* v___x_1813_; 
lean_dec(v___x_1786_);
lean_dec(v_decl_1691_);
v___x_1813_ = lean_box(0);
v___y_1743_ = v_rhs_1784_;
v_otherwise_x3f_1744_ = v___x_1813_;
v_body_x3f_x3f_1745_ = v___x_1813_;
v___y_1746_ = v___y_1777_;
v___y_1747_ = v___y_1778_;
v___y_1748_ = v___y_1779_;
v___y_1749_ = v___y_1780_;
v___y_1750_ = v___y_1781_;
v___y_1751_ = v___y_1782_;
goto v___jp_1742_;
}
}
}
}
else
{
lean_object* v___x_1836_; lean_object* v_x_1837_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v_x_1837_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1836_);
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1837_);
v___x_1852_ = l_Lean_Syntax_isOfKind(v_x_1837_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec(v_x_1837_);
v___x_1853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1854_ = lean_box(0);
v___x_1855_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1854_, v___x_1852_);
v___x_1856_ = l_Std_Format_defWidth;
v___x_1857_ = l_Std_Format_pretty(v___x_1855_, v___x_1856_, v___x_1836_, v___x_1836_);
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1853_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1859_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1861_);
v___x_1863_ = l_Lean_Syntax_isNone(v___x_1862_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; 
lean_inc(v___x_1862_);
v___x_1864_ = l_Lean_Syntax_matchesNull(v___x_1862_, v___x_1861_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v___x_1862_);
lean_dec(v_x_1837_);
v___x_1865_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1866_ = lean_box(0);
v___x_1867_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1866_, v___x_1864_);
v___x_1868_ = l_Std_Format_defWidth;
v___x_1869_ = l_Std_Format_pretty(v___x_1867_, v___x_1868_, v___x_1836_, v___x_1836_);
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1865_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1871_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1873_ = l_Lean_Syntax_getArg(v___x_1862_, v___x_1836_);
lean_dec(v___x_1862_);
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1875_ = l_Lean_Syntax_isOfKind(v___x_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_x_1837_);
v___x_1876_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1877_ = lean_box(0);
v___x_1878_ = l_Lean_Syntax_formatStx(v_decl_1691_, v___x_1877_, v___x_1875_);
v___x_1879_ = l_Std_Format_defWidth;
v___x_1880_ = l_Std_Format_pretty(v___x_1878_, v___x_1879_, v___x_1836_, v___x_1836_);
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1876_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1882_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1883_;
}
else
{
v___y_1839_ = v_a_1692_;
v___y_1840_ = v_a_1693_;
v___y_1841_ = v_a_1694_;
v___y_1842_ = v_a_1695_;
v___y_1843_ = v_a_1696_;
v___y_1844_ = v_a_1697_;
goto v___jp_1838_;
}
}
}
else
{
lean_dec(v___x_1862_);
v___y_1839_ = v_a_1692_;
v___y_1840_ = v_a_1693_;
v___y_1841_ = v_a_1694_;
v___y_1842_ = v_a_1695_;
v___y_1843_ = v_a_1696_;
v___y_1844_ = v_a_1697_;
goto v___jp_1838_;
}
}
v___jp_1838_:
{
lean_object* v___x_1845_; lean_object* v_rhs_1846_; 
v___x_1845_ = lean_unsigned_to_nat(3u);
v_rhs_1846_ = l_Lean_Syntax_getArg(v_decl_1691_, v___x_1845_);
lean_dec(v_decl_1691_);
if (v_reassignment_1690_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_x_1837_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1700_ = v___y_1842_;
v___y_1701_ = v___y_1840_;
v___y_1702_ = v___y_1839_;
v___y_1703_ = v___y_1844_;
v___y_1704_ = v___y_1843_;
v___y_1705_ = v___y_1841_;
v___y_1706_ = v_rhs_1846_;
v___y_1707_ = v___x_1847_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_mk_empty_array_with_capacity(v___x_1848_);
v___x_1850_ = lean_array_push(v___x_1849_, v_x_1837_);
v___y_1700_ = v___y_1842_;
v___y_1701_ = v___y_1840_;
v___y_1702_ = v___y_1839_;
v___y_1703_ = v___y_1844_;
v___y_1704_ = v___y_1843_;
v___y_1705_ = v___y_1841_;
v___y_1706_ = v_rhs_1846_;
v___y_1707_ = v___x_1850_;
goto v___jp_1699_;
}
}
}
v___jp_1699_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___y_1706_);
v___x_1709_ = lean_box(0);
v___x_1710_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1707_, v___x_1708_, v___x_1709_, v___x_1709_, v___y_1702_, v___y_1701_, v___y_1705_, v___y_1700_, v___y_1704_, v___y_1703_);
return v___x_1710_;
}
v___jp_1711_:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___y_1713_);
if (lean_obj_tag(v___y_1714_) == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1715_, v___x_1722_, v___y_1712_, v___x_1723_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1724_;
}
else
{
lean_object* v_val_1725_; lean_object* v___x_1726_; 
v_val_1725_ = lean_ctor_get(v___y_1714_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v___y_1714_, 1);
v___x_1726_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1715_, v___x_1722_, v___y_1712_, v_val_1725_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2012_);
return v___x_2021_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
lean_inc(v_a_2022_);
v___x_2023_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_2022_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2024_, v_b_2012_);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2011_, v___x_2026_);
v_i_2011_ = v___x_2027_;
v_b_2012_ = v___x_2025_;
goto _start;
}
else
{
lean_dec_ref(v_b_2012_);
return v___x_2023_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2058_, lean_object* v_as_2059_, size_t v_sz_2060_, size_t v_i_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_a_2071_; uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_lt(v_i_2061_, v_sz_2060_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_b_2062_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; lean_object* v_a_2078_; uint8_t v___x_2079_; 
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2078_ = lean_array_uget_borrowed(v_as_2059_, v_i_2061_);
lean_inc(v_a_2078_);
v___x_2079_ = l_Lean_Syntax_isOfKind(v_a_2078_, v___x_2077_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_dec_ref_known(v___x_2080_, 1);
v_a_2071_ = v_b_2062_;
goto v___jp_2070_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_b_2062_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___y_2091_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2089_ = lean_unsigned_to_nat(3u);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = l_Lean_Syntax_getArg(v_a_2078_, v___x_2108_);
v___x_2110_ = l_Lean_Syntax_getArgs(v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2113_ = lean_array_get_size(v___x_2110_);
v___x_2114_ = lean_nat_dec_lt(v___x_2111_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_dec_ref(v___x_2110_);
v___y_2091_ = v___x_2112_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; lean_object* v_snd_2120_; 
v___x_2115_ = lean_box(v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2112_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2113_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2079_, v___x_2058_, v___x_2110_, v___x_2117_, v___x_2118_, v___x_2116_);
lean_dec_ref(v___x_2110_);
v_snd_2120_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v___x_2119_);
v___y_2091_ = v_snd_2120_;
goto v___jp_2090_;
}
v___jp_2090_:
{
size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_sz_2092_ = lean_array_size(v___y_2091_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2092_, v___x_2093_, v___y_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
v_a_2071_ = v_b_2062_;
goto v___jp_2070_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_b_2062_);
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
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2094_, 1);
v___x_2104_ = l_Lean_Syntax_getArg(v_a_2078_, v___x_2089_);
v___x_2105_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2104_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2062_, v_a_2106_);
v_a_2071_ = v___x_2107_;
goto v___jp_2070_;
}
else
{
lean_dec_ref(v_b_2062_);
return v___x_2105_;
}
}
}
}
}
v___jp_2070_:
{
size_t v___x_2072_; size_t v___x_2073_; 
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2061_, v___x_2072_);
v_i_2061_ = v___x_2073_;
v_b_2062_ = v_a_2071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2121_, size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_a_2133_; uint8_t v___x_2137_; 
v___x_2137_ = lean_usize_dec_lt(v_i_2123_, v_sz_2122_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_b_2124_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v_a_2140_ = lean_array_uget_borrowed(v_as_2121_, v_i_2123_);
v___x_2153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2140_);
v___x_2154_ = l_Lean_Syntax_isOfKind(v_a_2140_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2140_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v_a_2140_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2158_ = lean_box(0);
lean_inc(v_a_2140_);
v___x_2159_ = l_Lean_Syntax_formatStx(v_a_2140_, v___x_2158_, v___x_2156_);
v___x_2160_ = l_Std_Format_defWidth;
v___x_2161_ = l_Std_Format_pretty(v___x_2159_, v___x_2160_, v___x_2139_, v___x_2139_);
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2163_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_dec_ref_known(v___x_2164_, 1);
v_a_2133_ = v_b_2124_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_b_2124_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = l_Lean_Syntax_getArg(v_a_2140_, v___x_2173_);
v___x_2175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2174_);
v___x_2176_ = l_Lean_Syntax_isOfKind(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v___x_2174_);
v___x_2177_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2178_ = lean_box(0);
lean_inc(v_a_2140_);
v___x_2179_ = l_Lean_Syntax_formatStx(v_a_2140_, v___x_2178_, v___x_2176_);
v___x_2180_ = l_Std_Format_defWidth;
v___x_2181_ = l_Std_Format_pretty(v___x_2179_, v___x_2180_, v___x_2139_, v___x_2139_);
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2177_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2183_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref_known(v___x_2184_, 1);
v_a_2133_ = v_b_2124_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_b_2124_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; size_t v_sz_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2193_ = l_Lean_Syntax_getArg(v___x_2174_, v___x_2139_);
lean_dec(v___x_2174_);
v___x_2194_ = l_Lean_Syntax_getArgs(v___x_2193_);
lean_dec(v___x_2193_);
v_sz_2195_ = lean_array_size(v___x_2194_);
v___x_2196_ = ((size_t)0ULL);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2154_, v___x_2194_, v_sz_2195_, v___x_2196_, v_b_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec_ref(v___x_2194_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_a_2133_ = v_a_2198_;
goto v___jp_2132_;
}
else
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_unsigned_to_nat(2u);
v___x_2200_ = l_Lean_Syntax_getArg(v_a_2140_, v___x_2199_);
v___x_2201_ = l_Lean_Syntax_isNone(v___x_2200_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = l_Lean_Syntax_matchesNull(v___x_2200_, v___x_2199_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2204_ = lean_box(0);
lean_inc(v_a_2140_);
v___x_2205_ = l_Lean_Syntax_formatStx(v_a_2140_, v___x_2204_, v___x_2202_);
v___x_2206_ = l_Std_Format_defWidth;
v___x_2207_ = l_Std_Format_pretty(v___x_2205_, v___x_2206_, v___x_2139_, v___x_2139_);
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2203_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2209_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_dec_ref_known(v___x_2210_, 1);
v_a_2133_ = v_b_2124_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v_b_2124_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
v___y_2142_ = v___y_2125_;
v___y_2143_ = v___y_2126_;
v___y_2144_ = v___y_2127_;
v___y_2145_ = v___y_2128_;
v___y_2146_ = v___y_2129_;
v___y_2147_ = v___y_2130_;
goto v___jp_2141_;
}
}
else
{
lean_dec(v___x_2200_);
v___y_2142_ = v___y_2125_;
v___y_2143_ = v___y_2126_;
v___y_2144_ = v___y_2127_;
v___y_2145_ = v___y_2128_;
v___y_2146_ = v___y_2129_;
v___y_2147_ = v___y_2130_;
goto v___jp_2141_;
}
}
v___jp_2141_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_unsigned_to_nat(4u);
v___x_2149_ = l_Lean_Syntax_getArg(v_a_2140_, v___x_2148_);
v___x_2150_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2149_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2151_, v_b_2124_);
v_a_2133_ = v___x_2152_;
goto v___jp_2132_;
}
else
{
lean_dec_ref(v_b_2124_);
return v___x_2150_;
}
}
}
v___jp_2132_:
{
size_t v___x_2134_; size_t v___x_2135_; 
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_add(v_i_2123_, v___x_2134_);
v_i_2123_ = v___x_2135_;
v_b_2124_ = v_a_2133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2219_) == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2230_; 
v_val_2229_ = lean_ctor_get(v_stx_x3f_2219_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_stx_x3f_2219_, 1);
v___x_2230_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2229_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2249_, lean_object* v_as_2250_, size_t v_sz_2251_, size_t v_i_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_a_2262_; uint8_t v___x_2266_; 
v___x_2266_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_b_2253_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; lean_object* v_a_2269_; uint8_t v___x_2270_; 
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2269_ = lean_array_uget_borrowed(v_as_2250_, v_i_2252_);
lean_inc(v_a_2269_);
v___x_2270_ = l_Lean_Syntax_isOfKind(v_a_2269_, v___x_2268_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_dec_ref_known(v___x_2271_, 1);
v_a_2262_ = v_b_2253_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_b_2253_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2280_; lean_object* v___y_2282_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2280_ = lean_unsigned_to_nat(3u);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = l_Lean_Syntax_getArg(v_a_2269_, v___x_2299_);
v___x_2301_ = l_Lean_Syntax_getArgs(v___x_2300_);
lean_dec(v___x_2300_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2304_ = lean_array_get_size(v___x_2301_);
v___x_2305_ = lean_nat_dec_lt(v___x_2302_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_dec_ref(v___x_2301_);
v___y_2282_ = v___x_2303_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; lean_object* v_snd_2311_; 
v___x_2306_ = lean_box(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2303_);
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2304_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2270_, v___x_2249_, v___x_2301_, v___x_2308_, v___x_2309_, v___x_2307_);
lean_dec_ref(v___x_2301_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v___y_2282_ = v_snd_2311_;
goto v___jp_2281_;
}
v___jp_2281_:
{
size_t v_sz_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v_sz_2283_ = lean_array_size(v___y_2282_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2283_, v___x_2284_, v___y_2282_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_dec_ref_known(v___x_2286_, 1);
v_a_2262_ = v_b_2253_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_b_2253_);
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
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec_ref_known(v___x_2285_, 1);
v___x_2295_ = l_Lean_Syntax_getArg(v_a_2269_, v___x_2280_);
v___x_2296_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2295_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2253_, v_a_2297_);
v_a_2262_ = v___x_2298_;
goto v___jp_2261_;
}
else
{
lean_dec_ref(v_b_2253_);
return v___x_2296_;
}
}
}
}
}
v___jp_2261_:
{
size_t v___x_2263_; size_t v___x_2264_; 
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2252_, v___x_2263_);
v_i_2252_ = v___x_2264_;
v_b_2253_ = v_a_2262_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2360_ = l_Lean_NameSet_empty;
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = 0;
v___x_2363_ = 1;
v___x_2364_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2364_, 0, v___x_2361_);
lean_ctor_set(v___x_2364_, 1, v___x_2360_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2, v___x_2363_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2 + 1, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2 + 2, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2 + 3, v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v___y_2374_; lean_object* v_bodyInfo_2375_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2395_; lean_object* v_bodyInfo_2396_; lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2399_ = lean_st_ref_get(v_a_2371_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_env_2400_);
lean_dec(v___x_2399_);
lean_inc(v_stx_2365_);
v___x_2401_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2401_, 0, v_env_2400_);
lean_closure_set(v___x_2401_, 1, v_stx_2365_);
v___x_2402_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2401_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_5108_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_5108_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_5108_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
if (lean_obj_tag(v_a_2403_) == 1)
{
lean_object* v_val_2407_; lean_object* v_snd_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_del_object(v___x_2405_);
lean_dec(v_stx_2365_);
v_val_2407_ = lean_ctor_get(v_a_2403_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v_a_2403_, 1);
v_snd_2408_ = lean_ctor_get(v_val_2407_, 1);
lean_inc(v_snd_2408_);
lean_dec(v_val_2407_);
v___x_2409_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2409_, 0, lean_box(0));
lean_closure_set(v___x_2409_, 1, v_snd_2408_);
v___x_2410_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2409_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v_stx_2365_ = v_a_2411_;
goto _start;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_a_2413_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2410_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2410_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___x_2603_; uint8_t v___x_2604_; uint8_t v___x_2605_; 
lean_dec(v_a_2403_);
v___x_2603_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2365_);
v___x_2604_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2603_);
v___x_2605_ = 1;
if (v___x_2604_ == 0)
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2365_);
v___x_2607_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2365_);
v___x_2609_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2365_);
v___x_2611_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2365_);
v___x_2613_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2365_);
v___x_2615_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
lean_del_object(v___x_2405_);
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2365_);
v___x_2617_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2365_);
v___x_2619_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; 
v___x_2620_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2365_);
v___x_2621_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2365_);
v___x_2683_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2365_);
v___x_2685_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2365_);
v___x_2687_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2365_);
v___x_2689_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2365_);
v___x_2691_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2365_);
v___x_2693_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2365_);
v___x_2695_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; uint8_t v___x_2697_; lean_object* v___y_2699_; uint8_t v___y_2700_; lean_object* v___y_2701_; uint8_t v___y_2702_; 
v___x_2696_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2365_);
v___x_2697_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2365_);
v___x_2706_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2365_);
v___x_2708_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2365_);
v___x_2710_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2365_);
v___x_2712_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2365_);
v___x_2714_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2365_);
v___x_2716_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2365_);
v___x_2718_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2365_);
v___x_2720_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2365_);
v___x_2722_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2365_);
v___x_2724_ = l_Lean_Syntax_isOfKind(v_stx_2365_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v_env_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_inc_n(v_stx_2365_, 2);
v___x_2725_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2726_ = lean_st_ref_get(v_a_2371_);
v_env_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_ref(v_env_2727_);
lean_dec(v___x_2726_);
v___x_2728_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2729_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2728_, v_env_2727_, v___x_2725_);
v___x_2730_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2731_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2729_, v___x_2730_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_2729_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2762_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2762_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2762_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_fst_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2760_; 
v_fst_2736_ = lean_ctor_get(v_a_2732_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2732_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v_a_2732_, 1);
lean_dec(v_unused_2761_);
v___x_2738_ = v_a_2732_;
v_isShared_2739_ = v_isSharedCheck_2760_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_fst_2736_);
lean_dec(v_a_2732_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2760_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
if (lean_obj_tag(v_fst_2736_) == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_del_object(v___x_2734_);
v___x_2740_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2741_ = l_Lean_MessageData_ofName(v___x_2725_);
lean_inc_ref(v___x_2741_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 7);
lean_ctor_set(v___x_2738_, 1, v___x_2741_);
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2743_ = v___x_2738_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2744_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2747_ = l_Lean_indentD(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2745_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v___x_2741_);
v___x_2752_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2753_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2754_;
}
}
else
{
lean_object* v_val_2756_; lean_object* v___x_2758_; 
lean_del_object(v___x_2738_);
lean_dec(v___x_2725_);
lean_dec(v_stx_2365_);
v_val_2756_ = lean_ctor_get(v_fst_2736_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v_fst_2736_, 1);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v_val_2756_);
v___x_2758_ = v___x_2734_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_val_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v___x_2725_);
lean_dec(v_stx_2365_);
v_a_2763_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2731_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2731_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___y_2775_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_unsigned_to_nat(5u);
v___x_2773_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2772_);
v___x_2784_ = lean_unsigned_to_nat(6u);
v___x_2785_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2784_);
lean_dec(v_stx_2365_);
v___x_2786_ = l_Lean_Syntax_getOptional_x3f(v___x_2785_);
lean_dec(v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_box(0);
v___y_2775_ = v___x_2787_;
goto v___jp_2774_;
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_val_2788_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_val_2788_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_val_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
v___y_2775_ = v___x_2793_;
goto v___jp_2774_;
}
}
}
v___jp_2774_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2773_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2776_) == 0)
{
if (lean_obj_tag(v___y_2775_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Lean_NameSet_empty;
v___x_2779_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2779_, 0, v___x_2771_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*2, v___x_2722_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*2 + 1, v___x_2722_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*2 + 2, v___x_2722_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*2 + 3, v___x_2722_);
v___y_2374_ = v_a_2777_;
v_bodyInfo_2375_ = v___x_2779_;
goto v___jp_2373_;
}
else
{
lean_object* v_a_2780_; lean_object* v_val_2781_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2776_, 1);
v_val_2781_ = lean_ctor_get(v___y_2775_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___y_2775_, 1);
v___x_2782_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2781_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___y_2374_ = v_a_2780_;
v_bodyInfo_2375_ = v_a_2783_;
goto v___jp_2373_;
}
else
{
lean_dec(v_a_2780_);
return v___x_2782_;
}
}
}
else
{
lean_dec(v___y_2775_);
return v___x_2776_;
}
}
}
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___y_2800_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_unsigned_to_nat(5u);
v___x_2798_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2797_);
v___x_2809_ = lean_unsigned_to_nat(6u);
v___x_2810_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2809_);
lean_dec(v_stx_2365_);
v___x_2811_ = l_Lean_Syntax_getOptional_x3f(v___x_2810_);
lean_dec(v___x_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_box(0);
v___y_2800_ = v___x_2812_;
goto v___jp_2799_;
}
else
{
lean_object* v_val_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_val_2813_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2811_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_val_2813_);
lean_dec(v___x_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_val_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
v___y_2800_ = v___x_2818_;
goto v___jp_2799_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2798_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2801_) == 0)
{
if (lean_obj_tag(v___y_2800_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = l_Lean_NameSet_empty;
v___x_2804_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2804_, 0, v___x_2796_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*2, v___x_2720_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*2 + 1, v___x_2720_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*2 + 2, v___x_2720_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*2 + 3, v___x_2720_);
v___y_2395_ = v_a_2802_;
v_bodyInfo_2396_ = v___x_2804_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2805_; lean_object* v_val_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2801_, 1);
v_val_2806_ = lean_ctor_get(v___y_2800_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v___y_2800_, 1);
v___x_2807_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2806_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___y_2395_ = v_a_2805_;
v_bodyInfo_2396_ = v_a_2808_;
goto v___jp_2394_;
}
else
{
lean_dec(v_a_2805_);
return v___x_2807_;
}
}
}
else
{
lean_dec(v___y_2800_);
return v___x_2801_;
}
}
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = lean_unsigned_to_nat(1u);
v___x_3036_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2822_);
v___x_3037_ = l_Lean_Syntax_isNone(v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = lean_unsigned_to_nat(5u);
v___x_3039_ = l_Lean_Syntax_matchesNull(v___x_3036_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_env_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3040_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3041_ = lean_st_ref_get(v_a_2371_);
v_env_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc_ref(v_env_3042_);
lean_dec(v___x_3041_);
v___x_3043_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3044_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3043_, v_env_3042_, v___x_3040_);
v___x_3045_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3046_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3044_, v___x_3045_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3044_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3077_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3077_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3077_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_fst_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3075_; 
v_fst_3051_ = lean_ctor_get(v_a_3047_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_a_3047_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v_a_3047_, 1);
lean_dec(v_unused_3076_);
v___x_3053_ = v_a_3047_;
v_isShared_3054_ = v_isSharedCheck_3075_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_fst_3051_);
lean_dec(v_a_3047_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3075_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
if (lean_obj_tag(v_fst_3051_) == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
lean_del_object(v___x_3049_);
v___x_3055_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3056_ = l_Lean_MessageData_ofName(v___x_3040_);
lean_inc_ref(v___x_3056_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 7);
lean_ctor_set(v___x_3053_, 1, v___x_3056_);
lean_ctor_set(v___x_3053_, 0, v___x_3055_);
v___x_3058_ = v___x_3053_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3059_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3062_ = l_Lean_indentD(v___x_3061_);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3060_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___x_3056_);
v___x_3067_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3068_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3069_;
}
}
else
{
lean_object* v_val_3071_; lean_object* v___x_3073_; 
lean_del_object(v___x_3053_);
lean_dec(v___x_3040_);
lean_dec(v_stx_2365_);
v_val_3071_ = lean_ctor_get(v_fst_3051_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v_fst_3051_, 1);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v_val_3071_);
v___x_3073_ = v___x_3049_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_val_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___x_3040_);
lean_dec(v_stx_2365_);
v_a_3078_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3046_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3046_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
v___y_2824_ = v_a_2366_;
v___y_2825_ = v_a_2367_;
v___y_2826_ = v_a_2368_;
v___y_2827_ = v_a_2369_;
v___y_2828_ = v_a_2370_;
v___y_2829_ = v_a_2371_;
goto v___jp_2823_;
}
}
else
{
lean_dec(v___x_3036_);
v___y_2824_ = v_a_2366_;
v___y_2825_ = v_a_2367_;
v___y_2826_ = v_a_2368_;
v___y_2827_ = v_a_2369_;
v___y_2828_ = v_a_2370_;
v___y_2829_ = v_a_2371_;
goto v___jp_2823_;
}
v___jp_2823_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2830_ = lean_unsigned_to_nat(4u);
v___x_2831_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2830_);
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2831_);
v___x_2833_ = l_Lean_Syntax_isOfKind(v___x_2831_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_env_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_dec(v___x_2831_);
lean_inc_n(v_stx_2365_, 2);
v___x_2834_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2835_ = lean_st_ref_get(v___y_2829_);
v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2836_);
lean_dec(v___x_2835_);
v___x_2837_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2838_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2837_, v_env_2836_, v___x_2834_);
v___x_2839_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2840_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2838_, v___x_2839_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2838_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2871_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2871_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2871_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_fst_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2869_; 
v_fst_2845_ = lean_ctor_get(v_a_2841_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2841_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_a_2841_, 1);
lean_dec(v_unused_2870_);
v___x_2847_ = v_a_2841_;
v_isShared_2848_ = v_isSharedCheck_2869_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_fst_2845_);
lean_dec(v_a_2841_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2869_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
if (lean_obj_tag(v_fst_2845_) == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_del_object(v___x_2843_);
v___x_2849_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2850_ = l_Lean_MessageData_ofName(v___x_2834_);
lean_inc_ref(v___x_2850_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 7);
lean_ctor_set(v___x_2847_, 1, v___x_2850_);
lean_ctor_set(v___x_2847_, 0, v___x_2849_);
v___x_2852_ = v___x_2847_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2856_ = l_Lean_indentD(v___x_2855_);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2854_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2857_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___x_2850_);
v___x_2861_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2862_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2863_;
}
}
else
{
lean_object* v_val_2865_; lean_object* v___x_2867_; 
lean_del_object(v___x_2847_);
lean_dec(v___x_2834_);
lean_dec(v_stx_2365_);
v_val_2865_ = lean_ctor_get(v_fst_2845_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v_fst_2845_, 1);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_val_2865_);
v___x_2867_ = v___x_2843_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_val_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v___x_2834_);
lean_dec(v_stx_2365_);
v_a_2872_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2840_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2840_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; size_t v_sz_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2880_ = l_Lean_Syntax_getArg(v___x_2831_, v___x_2821_);
v___x_2881_ = l_Lean_Syntax_getArgs(v___x_2880_);
lean_dec(v___x_2880_);
v_sz_2882_ = lean_array_size(v___x_2881_);
v___x_2883_ = ((size_t)0ULL);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2882_, v___x_2883_, v___x_2881_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v_env_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v___x_2831_);
lean_inc_n(v_stx_2365_, 2);
v___x_2885_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2886_ = lean_st_ref_get(v___y_2829_);
v_env_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc_ref(v_env_2887_);
lean_dec(v___x_2886_);
v___x_2888_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2889_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2888_, v_env_2887_, v___x_2885_);
v___x_2890_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2891_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2889_, v___x_2890_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2889_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2922_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_fst_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2920_; 
v_fst_2896_ = lean_ctor_get(v_a_2892_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_a_2892_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v_a_2892_, 1);
lean_dec(v_unused_2921_);
v___x_2898_ = v_a_2892_;
v_isShared_2899_ = v_isSharedCheck_2920_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_fst_2896_);
lean_dec(v_a_2892_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2920_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
if (lean_obj_tag(v_fst_2896_) == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_del_object(v___x_2894_);
v___x_2900_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2901_ = l_Lean_MessageData_ofName(v___x_2885_);
lean_inc_ref(v___x_2901_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set_tag(v___x_2898_, 7);
lean_ctor_set(v___x_2898_, 1, v___x_2901_);
lean_ctor_set(v___x_2898_, 0, v___x_2900_);
v___x_2903_ = v___x_2898_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2904_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2907_ = l_Lean_indentD(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2905_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set(v___x_2911_, 1, v___x_2901_);
v___x_2912_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2913_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2914_;
}
}
else
{
lean_object* v_val_2916_; lean_object* v___x_2918_; 
lean_del_object(v___x_2898_);
lean_dec(v___x_2885_);
lean_dec(v_stx_2365_);
v_val_2916_ = lean_ctor_get(v_fst_2896_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_fst_2896_, 1);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v_val_2916_);
v___x_2918_ = v___x_2894_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_val_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v___x_2885_);
lean_dec(v_stx_2365_);
v_a_2923_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2891_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2891_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_val_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_val_2931_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2932_ = l_Lean_Syntax_getArg(v___x_2831_, v___x_2822_);
lean_dec(v___x_2831_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_2932_);
v___x_2934_ = l_Lean_Syntax_isOfKind(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v___x_2932_);
lean_dec(v_val_2931_);
lean_inc_n(v_stx_2365_, 2);
v___x_2935_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2936_ = lean_st_ref_get(v___y_2829_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2938_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2939_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2938_, v_env_2937_, v___x_2935_);
v___x_2940_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2941_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2939_, v___x_2940_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2939_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2972_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2972_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2972_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v_fst_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2970_; 
v_fst_2946_ = lean_ctor_get(v_a_2942_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_a_2942_);
if (v_isSharedCheck_2970_ == 0)
{
lean_object* v_unused_2971_; 
v_unused_2971_ = lean_ctor_get(v_a_2942_, 1);
lean_dec(v_unused_2971_);
v___x_2948_ = v_a_2942_;
v_isShared_2949_ = v_isSharedCheck_2970_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_fst_2946_);
lean_dec(v_a_2942_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2970_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
if (lean_obj_tag(v_fst_2946_) == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
lean_del_object(v___x_2944_);
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2951_ = l_Lean_MessageData_ofName(v___x_2935_);
lean_inc_ref(v___x_2951_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 7);
lean_ctor_set(v___x_2948_, 1, v___x_2951_);
lean_ctor_set(v___x_2948_, 0, v___x_2950_);
v___x_2953_ = v___x_2948_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2957_ = l_Lean_indentD(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2951_);
v___x_2962_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2963_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2964_;
}
}
else
{
lean_object* v_val_2966_; lean_object* v___x_2968_; 
lean_del_object(v___x_2948_);
lean_dec(v___x_2935_);
lean_dec(v_stx_2365_);
v_val_2966_ = lean_ctor_get(v_fst_2946_, 0);
lean_inc(v_val_2966_);
lean_dec_ref_known(v_fst_2946_, 1);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v_val_2966_);
v___x_2968_ = v___x_2944_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_val_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v___x_2935_);
lean_dec(v_stx_2365_);
v_a_2973_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2941_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2941_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2981_ = l_Lean_Syntax_getArg(v___x_2932_, v___x_2822_);
v___x_2982_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_2983_ = l_Lean_Syntax_isOfKind(v___x_2981_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_env_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v___x_2932_);
lean_dec(v_val_2931_);
lean_inc_n(v_stx_2365_, 2);
v___x_2984_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2985_ = lean_st_ref_get(v___y_2829_);
v_env_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_env_2986_);
lean_dec(v___x_2985_);
v___x_2987_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2988_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2987_, v_env_2986_, v___x_2984_);
v___x_2989_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2990_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2988_, v___x_2989_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3021_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3021_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3021_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_fst_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3019_; 
v_fst_2995_ = lean_ctor_get(v_a_2991_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_a_2991_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_a_2991_, 1);
lean_dec(v_unused_3020_);
v___x_2997_ = v_a_2991_;
v_isShared_2998_ = v_isSharedCheck_3019_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_fst_2995_);
lean_dec(v_a_2991_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3019_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
if (lean_obj_tag(v_fst_2995_) == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_del_object(v___x_2993_);
v___x_2999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3000_ = l_Lean_MessageData_ofName(v___x_2984_);
lean_inc_ref(v___x_3000_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set_tag(v___x_2997_, 7);
lean_ctor_set(v___x_2997_, 1, v___x_3000_);
lean_ctor_set(v___x_2997_, 0, v___x_2999_);
v___x_3002_ = v___x_2997_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3003_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3006_ = l_Lean_indentD(v___x_3005_);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3004_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3000_);
v___x_3011_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3012_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_3013_;
}
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3017_; 
lean_del_object(v___x_2997_);
lean_dec(v___x_2984_);
lean_dec(v_stx_2365_);
v_val_3015_ = lean_ctor_get(v_fst_2995_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v_fst_2995_, 1);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_val_3015_);
v___x_3017_ = v___x_2993_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_val_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v___x_2984_);
lean_dec(v_stx_2365_);
v_a_3022_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2990_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2990_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_dec(v_stx_2365_);
v___x_3030_ = lean_unsigned_to_nat(3u);
v___x_3031_ = l_Lean_Syntax_getArg(v___x_2932_, v___x_3030_);
lean_dec(v___x_2932_);
v___x_3032_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3031_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; size_t v_sz_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v_sz_3034_ = lean_array_size(v_val_2931_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2931_, v_sz_3034_, v___x_2883_, v_a_3033_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_val_2931_);
return v___x_3035_;
}
else
{
lean_dec(v_val_2931_);
return v___x_3032_;
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
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v_stx_2365_);
v___x_3086_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_stx_2365_);
v___x_3088_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v_stx_2365_);
v___x_3090_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v_stx_2365_);
v___x_3092_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v_stx_2365_);
v___x_3094_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3096_ = lean_unsigned_to_nat(2u);
v___x_3097_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3096_);
v___x_3098_ = l_Lean_Syntax_getArgs(v___x_3097_);
lean_dec(v___x_3097_);
v_sz_3099_ = lean_array_size(v___x_3098_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3099_, v___x_3100_, v___x_3098_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_env_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3102_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3103_ = lean_st_ref_get(v_a_2371_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_env_3104_);
lean_dec(v___x_3103_);
v___x_3105_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3106_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3105_, v_env_3104_, v___x_3102_);
v___x_3107_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3108_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3106_, v___x_3107_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3139_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3139_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3139_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v_fst_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3137_; 
v_fst_3113_ = lean_ctor_get(v_a_3109_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3109_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v_a_3109_, 1);
lean_dec(v_unused_3138_);
v___x_3115_ = v_a_3109_;
v_isShared_3116_ = v_isSharedCheck_3137_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_fst_3113_);
lean_dec(v_a_3109_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3137_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
if (lean_obj_tag(v_fst_3113_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
lean_del_object(v___x_3111_);
v___x_3117_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3118_ = l_Lean_MessageData_ofName(v___x_3102_);
lean_inc_ref(v___x_3118_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set_tag(v___x_3115_, 7);
lean_ctor_set(v___x_3115_, 1, v___x_3118_);
lean_ctor_set(v___x_3115_, 0, v___x_3117_);
v___x_3120_ = v___x_3115_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3121_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3120_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3124_ = l_Lean_indentD(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3122_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3118_);
v___x_3129_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3130_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3131_;
}
}
else
{
lean_object* v_val_3133_; lean_object* v___x_3135_; 
lean_del_object(v___x_3115_);
lean_dec(v___x_3102_);
lean_dec(v_stx_2365_);
v_val_3133_ = lean_ctor_get(v_fst_3113_, 0);
lean_inc(v_val_3133_);
lean_dec_ref_known(v_fst_3113_, 1);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v_val_3133_);
v___x_3135_ = v___x_3111_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_val_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v___x_3102_);
lean_dec(v_stx_2365_);
v_a_3140_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3108_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3108_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_val_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3282_; 
v_val_3148_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3150_ = v___x_3101_;
v_isShared_3151_ = v_isSharedCheck_3282_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_val_3148_);
lean_dec(v___x_3101_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3282_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_finSeq_x3f_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3152_);
v___x_3177_ = lean_unsigned_to_nat(3u);
v___x_3178_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3177_);
v___x_3179_ = l_Lean_Syntax_isNone(v___x_3178_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
lean_inc(v___x_3178_);
v___x_3180_ = l_Lean_Syntax_matchesNull(v___x_3178_, v___x_3152_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_env_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v___x_3178_);
lean_dec(v___x_3153_);
lean_del_object(v___x_3150_);
lean_dec(v_val_3148_);
lean_inc_n(v_stx_2365_, 2);
v___x_3181_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3182_ = lean_st_ref_get(v_a_2371_);
v_env_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_env_3183_);
lean_dec(v___x_3182_);
v___x_3184_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3185_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3184_, v_env_3183_, v___x_3181_);
v___x_3186_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3187_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3185_, v___x_3186_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3185_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3218_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_fst_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3216_; 
v_fst_3192_ = lean_ctor_get(v_a_3188_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_a_3188_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v_a_3188_, 1);
lean_dec(v_unused_3217_);
v___x_3194_ = v_a_3188_;
v_isShared_3195_ = v_isSharedCheck_3216_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_fst_3192_);
lean_dec(v_a_3188_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3216_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
if (lean_obj_tag(v_fst_3192_) == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_del_object(v___x_3190_);
v___x_3196_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3197_ = l_Lean_MessageData_ofName(v___x_3181_);
lean_inc_ref(v___x_3197_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set_tag(v___x_3194_, 7);
lean_ctor_set(v___x_3194_, 1, v___x_3197_);
lean_ctor_set(v___x_3194_, 0, v___x_3196_);
v___x_3199_ = v___x_3194_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3200_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3199_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3203_ = l_Lean_indentD(v___x_3202_);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3201_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v___x_3197_);
v___x_3208_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3209_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3210_;
}
}
else
{
lean_object* v_val_3212_; lean_object* v___x_3214_; 
lean_del_object(v___x_3194_);
lean_dec(v___x_3181_);
lean_dec(v_stx_2365_);
v_val_3212_ = lean_ctor_get(v_fst_3192_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v_fst_3192_, 1);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v_val_3212_);
v___x_3214_ = v___x_3190_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_val_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v___x_3181_);
lean_dec(v_stx_2365_);
v_a_3219_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3187_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3187_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = l_Lean_Syntax_getArg(v___x_3178_, v___x_3227_);
lean_dec(v___x_3178_);
v___x_3229_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3228_);
v___x_3230_ = l_Lean_Syntax_isOfKind(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_env_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec(v___x_3228_);
lean_dec(v___x_3153_);
lean_del_object(v___x_3150_);
lean_dec(v_val_3148_);
lean_inc_n(v_stx_2365_, 2);
v___x_3231_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3232_ = lean_st_ref_get(v_a_2371_);
v_env_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc_ref(v_env_3233_);
lean_dec(v___x_3232_);
v___x_3234_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3235_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3234_, v_env_3233_, v___x_3231_);
v___x_3236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3237_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3235_, v___x_3236_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3235_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3268_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3268_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3268_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_fst_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3266_; 
v_fst_3242_ = lean_ctor_get(v_a_3238_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_a_3238_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v_a_3238_, 1);
lean_dec(v_unused_3267_);
v___x_3244_ = v_a_3238_;
v_isShared_3245_ = v_isSharedCheck_3266_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_fst_3242_);
lean_dec(v_a_3238_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3266_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
if (lean_obj_tag(v_fst_3242_) == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
lean_del_object(v___x_3240_);
v___x_3246_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3247_ = l_Lean_MessageData_ofName(v___x_3231_);
lean_inc_ref(v___x_3247_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 7);
lean_ctor_set(v___x_3244_, 1, v___x_3247_);
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3250_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3253_ = l_Lean_indentD(v___x_3252_);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3251_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v___x_3247_);
v___x_3258_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3259_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3260_;
}
}
else
{
lean_object* v_val_3262_; lean_object* v___x_3264_; 
lean_del_object(v___x_3244_);
lean_dec(v___x_3231_);
lean_dec(v_stx_2365_);
v_val_3262_ = lean_ctor_get(v_fst_3242_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v_fst_3242_, 1);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v_val_3262_);
v___x_3264_ = v___x_3240_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_val_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec(v___x_3231_);
lean_dec(v_stx_2365_);
v_a_3269_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3237_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3237_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_dec(v_stx_2365_);
v___x_3277_ = l_Lean_Syntax_getArg(v___x_3228_, v___x_3152_);
lean_dec(v___x_3228_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3277_);
v___x_3279_ = v___x_3150_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_finSeq_x3f_3155_ = v___x_3279_;
v___y_3156_ = v_a_2366_;
v___y_3157_ = v_a_2367_;
v___y_3158_ = v_a_2368_;
v___y_3159_ = v_a_2369_;
v___y_3160_ = v_a_2370_;
v___y_3161_ = v_a_2371_;
goto v___jp_3154_;
}
}
}
}
else
{
lean_object* v___x_3281_; 
lean_dec(v___x_3178_);
lean_del_object(v___x_3150_);
lean_dec(v_stx_2365_);
v___x_3281_ = lean_box(0);
v_finSeq_x3f_3155_ = v___x_3281_;
v___y_3156_ = v_a_2366_;
v___y_3157_ = v_a_2367_;
v___y_3158_ = v_a_2368_;
v___y_3159_ = v_a_2369_;
v___y_3160_ = v_a_2370_;
v___y_3161_ = v_a_2371_;
goto v___jp_3154_;
}
v___jp_3154_:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3153_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; size_t v_sz_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v_sz_3164_ = lean_array_size(v_val_3148_);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3148_, v_sz_3164_, v___x_3100_, v_a_3163_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v_val_3148_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3176_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3166_, v_a_3168_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
else
{
lean_dec(v_a_3166_);
return v___x_3167_;
}
}
else
{
lean_dec(v_finSeq_x3f_3155_);
return v___x_3165_;
}
}
else
{
lean_dec(v_finSeq_x3f_3155_);
lean_dec(v_val_3148_);
return v___x_3162_;
}
}
}
}
}
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_unsigned_to_nat(1u);
v___x_3407_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3284_);
v___x_3408_ = l_Lean_Syntax_isNone(v___x_3407_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
lean_inc(v___x_3407_);
v___x_3409_ = l_Lean_Syntax_matchesNull(v___x_3407_, v___x_3284_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v_env_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v___x_3407_);
lean_inc_n(v_stx_2365_, 2);
v___x_3410_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3411_ = lean_st_ref_get(v_a_2371_);
v_env_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc_ref(v_env_3412_);
lean_dec(v___x_3411_);
v___x_3413_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3414_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3413_, v_env_3412_, v___x_3410_);
v___x_3415_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3416_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3414_, v___x_3415_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3414_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3447_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3447_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3447_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3445_; 
v_fst_3421_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v_a_3417_, 1);
lean_dec(v_unused_3446_);
v___x_3423_ = v_a_3417_;
v_isShared_3424_ = v_isSharedCheck_3445_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_fst_3421_);
lean_dec(v_a_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3445_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
if (lean_obj_tag(v_fst_3421_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_del_object(v___x_3419_);
v___x_3425_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3426_ = l_Lean_MessageData_ofName(v___x_3410_);
lean_inc_ref(v___x_3426_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 7);
lean_ctor_set(v___x_3423_, 1, v___x_3426_);
lean_ctor_set(v___x_3423_, 0, v___x_3425_);
v___x_3428_ = v___x_3423_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3429_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3432_ = l_Lean_indentD(v___x_3431_);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3430_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___x_3426_);
v___x_3437_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3438_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3439_;
}
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3443_; 
lean_del_object(v___x_3423_);
lean_dec(v___x_3410_);
lean_dec(v_stx_2365_);
v_val_3441_ = lean_ctor_get(v_fst_3421_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v_fst_3421_, 1);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_val_3441_);
v___x_3443_ = v___x_3419_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_val_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v___x_3410_);
lean_dec(v_stx_2365_);
v_a_3448_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3416_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3416_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = l_Lean_Syntax_getArg(v___x_3407_, v___x_3283_);
lean_dec(v___x_3407_);
v___x_3457_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3458_ = l_Lean_Syntax_isOfKind(v___x_3456_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v_env_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3459_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3460_ = lean_st_ref_get(v_a_2371_);
v_env_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc_ref(v_env_3461_);
lean_dec(v___x_3460_);
v___x_3462_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3463_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3462_, v_env_3461_, v___x_3459_);
v___x_3464_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3465_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3463_, v___x_3464_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3463_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3496_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_fst_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3494_; 
v_fst_3470_ = lean_ctor_get(v_a_3466_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3466_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v_a_3466_, 1);
lean_dec(v_unused_3495_);
v___x_3472_ = v_a_3466_;
v_isShared_3473_ = v_isSharedCheck_3494_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_fst_3470_);
lean_dec(v_a_3466_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3494_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
if (lean_obj_tag(v_fst_3470_) == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_del_object(v___x_3468_);
v___x_3474_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3475_ = l_Lean_MessageData_ofName(v___x_3459_);
lean_inc_ref(v___x_3475_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 7);
lean_ctor_set(v___x_3472_, 1, v___x_3475_);
lean_ctor_set(v___x_3472_, 0, v___x_3474_);
v___x_3477_ = v___x_3472_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3478_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3481_ = l_Lean_indentD(v___x_3480_);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3479_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___x_3475_);
v___x_3486_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3487_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3488_;
}
}
else
{
lean_object* v_val_3490_; lean_object* v___x_3492_; 
lean_del_object(v___x_3472_);
lean_dec(v___x_3459_);
lean_dec(v_stx_2365_);
v_val_3490_ = lean_ctor_get(v_fst_3470_, 0);
lean_inc(v_val_3490_);
lean_dec_ref_known(v_fst_3470_, 1);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v_val_3490_);
v___x_3492_ = v___x_3468_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_val_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v___x_3459_);
lean_dec(v_stx_2365_);
v_a_3497_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3465_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3465_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
v___y_3302_ = v_a_2366_;
v___y_3303_ = v_a_2367_;
v___y_3304_ = v_a_2368_;
v___y_3305_ = v_a_2369_;
v___y_3306_ = v_a_2370_;
v___y_3307_ = v_a_2371_;
goto v___jp_3301_;
}
}
}
else
{
lean_dec(v___x_3407_);
v___y_3302_ = v_a_2366_;
v___y_3303_ = v_a_2367_;
v___y_3304_ = v_a_2368_;
v___y_3305_ = v_a_2369_;
v___y_3306_ = v_a_2370_;
v___y_3307_ = v_a_2371_;
goto v___jp_3301_;
}
v___jp_3285_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_unsigned_to_nat(3u);
v___x_3293_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3292_);
lean_dec(v_stx_2365_);
v___x_3294_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3293_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; uint8_t v_breaks_3296_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v_breaks_3296_ = lean_ctor_get_uint8(v_a_3295_, sizeof(void*)*2);
if (v_breaks_3296_ == 0)
{
uint8_t v_returnsEarly_3297_; lean_object* v_reassigns_3298_; 
v_returnsEarly_3297_ = lean_ctor_get_uint8(v_a_3295_, sizeof(void*)*2 + 2);
v_reassigns_3298_ = lean_ctor_get(v_a_3295_, 1);
lean_inc(v_reassigns_3298_);
lean_dec(v_a_3295_);
v___y_2699_ = v___x_3283_;
v___y_2700_ = v_returnsEarly_3297_;
v___y_2701_ = v_reassigns_3298_;
v___y_2702_ = v___x_2706_;
goto v___jp_2698_;
}
else
{
uint8_t v_returnsEarly_3299_; lean_object* v_reassigns_3300_; 
v_returnsEarly_3299_ = lean_ctor_get_uint8(v_a_3295_, sizeof(void*)*2 + 2);
v_reassigns_3300_ = lean_ctor_get(v_a_3295_, 1);
lean_inc(v_reassigns_3300_);
lean_dec(v_a_3295_);
v___y_2699_ = v___x_3284_;
v___y_2700_ = v_returnsEarly_3299_;
v___y_2701_ = v_reassigns_3300_;
v___y_2702_ = v___x_2697_;
goto v___jp_2698_;
}
}
else
{
return v___x_3294_;
}
}
v___jp_3301_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(2u);
v___x_3309_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3308_);
v___x_3310_ = l_Lean_Syntax_isNone(v___x_3309_);
if (v___x_3310_ == 0)
{
uint8_t v___x_3311_; 
lean_inc(v___x_3309_);
v___x_3311_ = l_Lean_Syntax_matchesNull(v___x_3309_, v___x_3284_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_env_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v___x_3309_);
lean_inc_n(v_stx_2365_, 2);
v___x_3312_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3313_ = lean_st_ref_get(v___y_3307_);
v_env_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc_ref(v_env_3314_);
lean_dec(v___x_3313_);
v___x_3315_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3316_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3315_, v_env_3314_, v___x_3312_);
v___x_3317_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3318_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3316_, v___x_3317_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___x_3316_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3349_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3349_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3349_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_fst_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3347_; 
v_fst_3323_ = lean_ctor_get(v_a_3319_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_a_3319_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v_a_3319_, 1);
lean_dec(v_unused_3348_);
v___x_3325_ = v_a_3319_;
v_isShared_3326_ = v_isSharedCheck_3347_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_fst_3323_);
lean_dec(v_a_3319_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3347_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_fst_3323_) == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
lean_del_object(v___x_3321_);
v___x_3327_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3328_ = l_Lean_MessageData_ofName(v___x_3312_);
lean_inc_ref(v___x_3328_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 7);
lean_ctor_set(v___x_3325_, 1, v___x_3328_);
lean_ctor_set(v___x_3325_, 0, v___x_3327_);
v___x_3330_ = v___x_3325_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3331_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3334_ = l_Lean_indentD(v___x_3333_);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3332_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___x_3328_);
v___x_3339_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3340_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
return v___x_3341_;
}
}
else
{
lean_object* v_val_3343_; lean_object* v___x_3345_; 
lean_del_object(v___x_3325_);
lean_dec(v___x_3312_);
lean_dec(v_stx_2365_);
v_val_3343_ = lean_ctor_get(v_fst_3323_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v_fst_3323_, 1);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v_val_3343_);
v___x_3345_ = v___x_3321_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_val_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v___x_3312_);
lean_dec(v_stx_2365_);
v_a_3350_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3318_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3318_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3358_ = l_Lean_Syntax_getArg(v___x_3309_, v___x_3283_);
lean_dec(v___x_3309_);
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3360_ = l_Lean_Syntax_isOfKind(v___x_3358_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v_env_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3361_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3362_ = lean_st_ref_get(v___y_3307_);
v_env_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc_ref(v_env_3363_);
lean_dec(v___x_3362_);
v___x_3364_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3365_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3364_, v_env_3363_, v___x_3361_);
v___x_3366_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3367_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3365_, v___x_3366_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___x_3365_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3398_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3398_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3398_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3396_; 
v_fst_3372_ = lean_ctor_get(v_a_3368_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v_a_3368_, 1);
lean_dec(v_unused_3397_);
v___x_3374_ = v_a_3368_;
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_fst_3372_);
lean_dec(v_a_3368_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
if (lean_obj_tag(v_fst_3372_) == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_del_object(v___x_3370_);
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3377_ = l_Lean_MessageData_ofName(v___x_3361_);
lean_inc_ref(v___x_3377_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 7);
lean_ctor_set(v___x_3374_, 1, v___x_3377_);
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3379_ = v___x_3374_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3380_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3383_ = l_Lean_indentD(v___x_3382_);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3381_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___x_3377_);
v___x_3388_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3389_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
return v___x_3390_;
}
}
else
{
lean_object* v_val_3392_; lean_object* v___x_3394_; 
lean_del_object(v___x_3374_);
lean_dec(v___x_3361_);
lean_dec(v_stx_2365_);
v_val_3392_ = lean_ctor_get(v_fst_3372_, 0);
lean_inc(v_val_3392_);
lean_dec_ref_known(v_fst_3372_, 1);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v_val_3392_);
v___x_3394_ = v___x_3370_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_val_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v___x_3361_);
lean_dec(v_stx_2365_);
v_a_3399_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3367_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3367_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
v___y_3286_ = v___y_3302_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3304_;
v___y_3289_ = v___y_3305_;
v___y_3290_ = v___y_3306_;
v___y_3291_ = v___y_3307_;
goto v___jp_3285_;
}
}
}
else
{
lean_dec(v___x_3309_);
v___y_3286_ = v___y_3302_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3304_;
v___y_3289_ = v___y_3305_;
v___y_3290_ = v___y_3306_;
v___y_3291_ = v___y_3307_;
goto v___jp_3285_;
}
}
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3642_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_unsigned_to_nat(1u);
v___x_3791_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3506_);
v___x_3792_ = l_Lean_Syntax_getArgs(v___x_3791_);
lean_dec(v___x_3791_);
v___x_3793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3794_ = lean_array_get_size(v___x_3792_);
v___x_3795_ = lean_nat_dec_lt(v___x_3505_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_dec_ref(v___x_3792_);
v___y_3642_ = v___x_3793_;
goto v___jp_3641_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; lean_object* v_snd_3801_; 
v___x_3796_ = lean_box(v___x_3795_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set(v___x_3797_, 1, v___x_3793_);
v___x_3798_ = ((size_t)0ULL);
v___x_3799_ = lean_usize_of_nat(v___x_3794_);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2697_, v___x_2695_, v___x_3792_, v___x_3798_, v___x_3799_, v___x_3797_);
lean_dec_ref(v___x_3792_);
v_snd_3801_ = lean_ctor_get(v___x_3800_, 1);
lean_inc(v_snd_3801_);
lean_dec_ref(v___x_3800_);
v___y_3642_ = v_snd_3801_;
goto v___jp_3641_;
}
v___jp_3507_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = lean_unsigned_to_nat(5u);
v___x_3515_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3514_);
lean_dec(v_stx_2365_);
v___x_3516_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3515_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3534_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3534_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3534_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
uint8_t v_returnsEarly_3521_; lean_object* v_reassigns_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3532_; 
v_returnsEarly_3521_ = lean_ctor_get_uint8(v_a_3517_, sizeof(void*)*2 + 2);
v_reassigns_3522_ = lean_ctor_get(v_a_3517_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3517_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v_a_3517_, 0);
lean_dec(v_unused_3533_);
v___x_3524_ = v_a_3517_;
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_reassigns_3522_);
lean_dec(v_a_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3506_);
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_reassigns_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3531_, sizeof(void*)*2 + 2, v_returnsEarly_3521_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*2, v___x_2695_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*2 + 1, v___x_2695_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*2 + 3, v___x_2695_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3527_);
v___x_3529_ = v___x_3519_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
else
{
return v___x_3516_;
}
}
v___jp_3535_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3542_ = lean_unsigned_to_nat(3u);
v___x_3543_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3542_);
v___x_3544_ = l_Lean_Syntax_isNone(v___x_3543_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
lean_inc(v___x_3543_);
v___x_3545_ = l_Lean_Syntax_matchesNull(v___x_3543_, v___x_3506_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v_env_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_dec(v___x_3543_);
lean_inc_n(v_stx_2365_, 2);
v___x_3546_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3547_ = lean_st_ref_get(v___y_3541_);
v_env_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc_ref(v_env_3548_);
lean_dec(v___x_3547_);
v___x_3549_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3550_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3549_, v_env_3548_, v___x_3546_);
v___x_3551_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3552_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3550_, v___x_3551_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___x_3550_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3583_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3583_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3583_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_fst_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3581_; 
v_fst_3557_ = lean_ctor_get(v_a_3553_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_a_3553_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v_a_3553_, 1);
lean_dec(v_unused_3582_);
v___x_3559_ = v_a_3553_;
v_isShared_3560_ = v_isSharedCheck_3581_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_fst_3557_);
lean_dec(v_a_3553_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3581_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
if (lean_obj_tag(v_fst_3557_) == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_del_object(v___x_3555_);
v___x_3561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3562_ = l_Lean_MessageData_ofName(v___x_3546_);
lean_inc_ref(v___x_3562_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 7);
lean_ctor_set(v___x_3559_, 1, v___x_3562_);
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3564_ = v___x_3559_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3565_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3568_ = l_Lean_indentD(v___x_3567_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3566_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v___x_3562_);
v___x_3573_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3574_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3575_;
}
}
else
{
lean_object* v_val_3577_; lean_object* v___x_3579_; 
lean_del_object(v___x_3559_);
lean_dec(v___x_3546_);
lean_dec(v_stx_2365_);
v_val_3577_ = lean_ctor_get(v_fst_3557_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v_fst_3557_, 1);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v_val_3577_);
v___x_3579_ = v___x_3555_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_val_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v___x_3546_);
lean_dec(v_stx_2365_);
v_a_3584_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3552_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3552_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3592_ = l_Lean_Syntax_getArg(v___x_3543_, v___x_3505_);
lean_dec(v___x_3543_);
v___x_3593_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3594_ = l_Lean_Syntax_isOfKind(v___x_3592_, v___x_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_env_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3595_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3596_ = lean_st_ref_get(v___y_3541_);
v_env_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_env_3597_);
lean_dec(v___x_3596_);
v___x_3598_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3599_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3598_, v_env_3597_, v___x_3595_);
v___x_3600_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3601_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3599_, v___x_3600_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___x_3599_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3632_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3632_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3632_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_fst_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3630_; 
v_fst_3606_ = lean_ctor_get(v_a_3602_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v_a_3602_, 1);
lean_dec(v_unused_3631_);
v___x_3608_ = v_a_3602_;
v_isShared_3609_ = v_isSharedCheck_3630_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_fst_3606_);
lean_dec(v_a_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3630_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
if (lean_obj_tag(v_fst_3606_) == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
lean_del_object(v___x_3604_);
v___x_3610_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3611_ = l_Lean_MessageData_ofName(v___x_3595_);
lean_inc_ref(v___x_3611_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 7);
lean_ctor_set(v___x_3608_, 1, v___x_3611_);
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3613_ = v___x_3608_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3617_ = l_Lean_indentD(v___x_3616_);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3615_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3611_);
v___x_3622_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3623_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3624_;
}
}
else
{
lean_object* v_val_3626_; lean_object* v___x_3628_; 
lean_del_object(v___x_3608_);
lean_dec(v___x_3595_);
lean_dec(v_stx_2365_);
v_val_3626_ = lean_ctor_get(v_fst_3606_, 0);
lean_inc(v_val_3626_);
lean_dec_ref_known(v_fst_3606_, 1);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v_val_3626_);
v___x_3628_ = v___x_3604_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_val_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___x_3595_);
lean_dec(v_stx_2365_);
v_a_3633_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3601_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3601_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3537_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3540_;
v___y_3513_ = v___y_3541_;
goto v___jp_3507_;
}
}
}
else
{
lean_dec(v___x_3543_);
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3537_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3540_;
v___y_3513_ = v___y_3541_;
goto v___jp_3507_;
}
}
v___jp_3641_:
{
size_t v_sz_3643_; size_t v___x_3644_; lean_object* v___x_3645_; 
v_sz_3643_ = lean_array_size(v___y_3642_);
v___x_3644_ = ((size_t)0ULL);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3643_, v___x_3644_, v___y_3642_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_env_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3646_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3647_ = lean_st_ref_get(v_a_2371_);
v_env_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc_ref(v_env_3648_);
lean_dec(v___x_3647_);
v___x_3649_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3650_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3649_, v_env_3648_, v___x_3646_);
v___x_3651_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3652_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3650_, v___x_3651_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3650_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3683_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3683_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3683_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v_fst_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3681_; 
v_fst_3657_ = lean_ctor_get(v_a_3653_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_a_3653_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; 
v_unused_3682_ = lean_ctor_get(v_a_3653_, 1);
lean_dec(v_unused_3682_);
v___x_3659_ = v_a_3653_;
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_fst_3657_);
lean_dec(v_a_3653_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3681_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
if (lean_obj_tag(v_fst_3657_) == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_del_object(v___x_3655_);
v___x_3661_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3662_ = l_Lean_MessageData_ofName(v___x_3646_);
lean_inc_ref(v___x_3662_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 7);
lean_ctor_set(v___x_3659_, 1, v___x_3662_);
lean_ctor_set(v___x_3659_, 0, v___x_3661_);
v___x_3664_ = v___x_3659_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3665_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3668_ = l_Lean_indentD(v___x_3667_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3666_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3669_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
lean_ctor_set(v___x_3672_, 1, v___x_3662_);
v___x_3673_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3674_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3675_;
}
}
else
{
lean_object* v_val_3677_; lean_object* v___x_3679_; 
lean_del_object(v___x_3659_);
lean_dec(v___x_3646_);
lean_dec(v_stx_2365_);
v_val_3677_ = lean_ctor_get(v_fst_3657_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_fst_3657_, 1);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_val_3677_);
v___x_3679_ = v___x_3655_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_val_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v___x_3646_);
lean_dec(v_stx_2365_);
v_a_3684_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3652_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3652_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
lean_dec_ref_known(v___x_3645_, 1);
v___x_3692_ = lean_unsigned_to_nat(2u);
v___x_3693_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3692_);
v___x_3694_ = l_Lean_Syntax_isNone(v___x_3693_);
if (v___x_3694_ == 0)
{
uint8_t v___x_3695_; 
lean_inc(v___x_3693_);
v___x_3695_ = l_Lean_Syntax_matchesNull(v___x_3693_, v___x_3506_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v_env_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec(v___x_3693_);
lean_inc_n(v_stx_2365_, 2);
v___x_3696_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3697_ = lean_st_ref_get(v_a_2371_);
v_env_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc_ref(v_env_3698_);
lean_dec(v___x_3697_);
v___x_3699_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3700_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3699_, v_env_3698_, v___x_3696_);
v___x_3701_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3702_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3700_, v___x_3701_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3700_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3733_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3733_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3733_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_fst_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3731_; 
v_fst_3707_ = lean_ctor_get(v_a_3703_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_a_3703_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_a_3703_, 1);
lean_dec(v_unused_3732_);
v___x_3709_ = v_a_3703_;
v_isShared_3710_ = v_isSharedCheck_3731_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_fst_3707_);
lean_dec(v_a_3703_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3731_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
if (lean_obj_tag(v_fst_3707_) == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_del_object(v___x_3705_);
v___x_3711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3712_ = l_Lean_MessageData_ofName(v___x_3696_);
lean_inc_ref(v___x_3712_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set_tag(v___x_3709_, 7);
lean_ctor_set(v___x_3709_, 1, v___x_3712_);
lean_ctor_set(v___x_3709_, 0, v___x_3711_);
v___x_3714_ = v___x_3709_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3718_ = l_Lean_indentD(v___x_3717_);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3716_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3712_);
v___x_3723_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3724_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3725_;
}
}
else
{
lean_object* v_val_3727_; lean_object* v___x_3729_; 
lean_del_object(v___x_3709_);
lean_dec(v___x_3696_);
lean_dec(v_stx_2365_);
v_val_3727_ = lean_ctor_get(v_fst_3707_, 0);
lean_inc(v_val_3727_);
lean_dec_ref_known(v_fst_3707_, 1);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v_val_3727_);
v___x_3729_ = v___x_3705_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_val_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v___x_3696_);
lean_dec(v_stx_2365_);
v_a_3734_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3702_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3702_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3742_ = l_Lean_Syntax_getArg(v___x_3693_, v___x_3505_);
lean_dec(v___x_3693_);
v___x_3743_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3744_ = l_Lean_Syntax_isOfKind(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_env_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3745_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3746_ = lean_st_ref_get(v_a_2371_);
v_env_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc_ref(v_env_3747_);
lean_dec(v___x_3746_);
v___x_3748_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3749_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3748_, v_env_3747_, v___x_3745_);
v___x_3750_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3751_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3749_, v___x_3750_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3749_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3782_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3782_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3782_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_fst_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3780_; 
v_fst_3756_ = lean_ctor_get(v_a_3752_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_a_3752_);
if (v_isSharedCheck_3780_ == 0)
{
lean_object* v_unused_3781_; 
v_unused_3781_ = lean_ctor_get(v_a_3752_, 1);
lean_dec(v_unused_3781_);
v___x_3758_ = v_a_3752_;
v_isShared_3759_ = v_isSharedCheck_3780_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_fst_3756_);
lean_dec(v_a_3752_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3780_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
if (lean_obj_tag(v_fst_3756_) == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3763_; 
lean_del_object(v___x_3754_);
v___x_3760_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3761_ = l_Lean_MessageData_ofName(v___x_3745_);
lean_inc_ref(v___x_3761_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 7);
lean_ctor_set(v___x_3758_, 1, v___x_3761_);
lean_ctor_set(v___x_3758_, 0, v___x_3760_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3767_ = l_Lean_indentD(v___x_3766_);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3765_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v___x_3761_);
v___x_3772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3773_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3774_;
}
}
else
{
lean_object* v_val_3776_; lean_object* v___x_3778_; 
lean_del_object(v___x_3758_);
lean_dec(v___x_3745_);
lean_dec(v_stx_2365_);
v_val_3776_ = lean_ctor_get(v_fst_3756_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v_fst_3756_, 1);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v_val_3776_);
v___x_3778_ = v___x_3754_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_val_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v___x_3745_);
lean_dec(v_stx_2365_);
v_a_3783_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3751_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3751_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
v___y_3536_ = v_a_2366_;
v___y_3537_ = v_a_2367_;
v___y_3538_ = v_a_2368_;
v___y_3539_ = v_a_2369_;
v___y_3540_ = v_a_2370_;
v___y_3541_ = v_a_2371_;
goto v___jp_3535_;
}
}
}
else
{
lean_dec(v___x_3693_);
v___y_3536_ = v_a_2366_;
v___y_3537_ = v_a_2367_;
v___y_3538_ = v_a_2368_;
v___y_3539_ = v_a_2369_;
v___y_3540_ = v_a_2370_;
v___y_3541_ = v_a_2371_;
goto v___jp_3535_;
}
}
}
}
v___jp_2698_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2703_, 0, v___y_2699_);
lean_ctor_set(v___x_2703_, 1, v___y_2701_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*2, v___x_2697_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*2 + 1, v___x_2697_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*2 + 2, v___y_2700_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*2 + 3, v___y_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_unsigned_to_nat(3u);
v___x_3804_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3803_);
lean_dec(v_stx_2365_);
v___x_3805_ = l_Lean_NameSet_empty;
v___x_3806_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3806_, 0, v___x_3802_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*2, v___x_2693_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*2 + 1, v___x_2693_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*2 + 2, v___x_2693_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*2 + 3, v___x_2693_);
v___x_3807_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3804_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3816_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3816_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3816_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3812_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3806_, v_a_3808_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3812_);
v___x_3814_ = v___x_3810_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_dec_ref_known(v___x_3806_, 2);
return v___x_3807_;
}
}
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; size_t v_sz_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = lean_unsigned_to_nat(4u);
v___x_3818_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3817_);
v___x_3819_ = l_Lean_Syntax_getArgs(v___x_3818_);
lean_dec(v___x_3818_);
v_sz_3820_ = lean_array_size(v___x_3819_);
v___x_3821_ = ((size_t)0ULL);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3820_, v___x_3821_, v___x_3819_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v_env_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
lean_inc_n(v_stx_2365_, 2);
v___x_3823_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3824_ = lean_st_ref_get(v_a_2371_);
v_env_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc_ref(v_env_3825_);
lean_dec(v___x_3824_);
v___x_3826_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3827_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3826_, v_env_3825_, v___x_3823_);
v___x_3828_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3829_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3827_, v___x_3828_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3827_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3860_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3860_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3860_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_fst_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3858_; 
v_fst_3834_ = lean_ctor_get(v_a_3830_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3830_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v_a_3830_, 1);
lean_dec(v_unused_3859_);
v___x_3836_ = v_a_3830_;
v_isShared_3837_ = v_isSharedCheck_3858_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_fst_3834_);
lean_dec(v_a_3830_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3858_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
if (lean_obj_tag(v_fst_3834_) == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_del_object(v___x_3832_);
v___x_3838_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3839_ = l_Lean_MessageData_ofName(v___x_3823_);
lean_inc_ref(v___x_3839_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set_tag(v___x_3836_, 7);
lean_ctor_set(v___x_3836_, 1, v___x_3839_);
lean_ctor_set(v___x_3836_, 0, v___x_3838_);
v___x_3841_ = v___x_3836_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3842_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3841_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3845_ = l_Lean_indentD(v___x_3844_);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3843_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
lean_ctor_set(v___x_3849_, 1, v___x_3839_);
v___x_3850_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3851_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3852_;
}
}
else
{
lean_object* v_val_3854_; lean_object* v___x_3856_; 
lean_del_object(v___x_3836_);
lean_dec(v___x_3823_);
lean_dec(v_stx_2365_);
v_val_3854_ = lean_ctor_get(v_fst_3834_, 0);
lean_inc(v_val_3854_);
lean_dec_ref_known(v_fst_3834_, 1);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v_val_3854_);
v___x_3856_ = v___x_3832_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_val_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v___x_3823_);
lean_dec(v_stx_2365_);
v_a_3861_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3829_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3829_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_val_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3956_; 
v_val_3869_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3871_ = v___x_3822_;
v_isShared_3872_ = v_isSharedCheck_3956_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_val_3869_);
lean_dec(v___x_3822_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3956_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v_elseSeq_x3f_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3873_ = lean_unsigned_to_nat(3u);
v___x_3874_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3873_);
v___x_3899_ = lean_unsigned_to_nat(5u);
v___x_3900_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3899_);
v___x_3901_ = l_Lean_Syntax_isNone(v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3900_);
v___x_3903_ = l_Lean_Syntax_matchesNull(v___x_3900_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v_env_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v___x_3900_);
lean_dec(v___x_3874_);
lean_del_object(v___x_3871_);
lean_dec(v_val_3869_);
lean_inc_n(v_stx_2365_, 2);
v___x_3904_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3905_ = lean_st_ref_get(v_a_2371_);
v_env_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref(v_env_3906_);
lean_dec(v___x_3905_);
v___x_3907_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3908_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3907_, v_env_3906_, v___x_3904_);
v___x_3909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3910_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3908_, v___x_3909_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_3908_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3941_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3941_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3941_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_fst_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3939_; 
v_fst_3915_ = lean_ctor_get(v_a_3911_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; 
v_unused_3940_ = lean_ctor_get(v_a_3911_, 1);
lean_dec(v_unused_3940_);
v___x_3917_ = v_a_3911_;
v_isShared_3918_ = v_isSharedCheck_3939_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_fst_3915_);
lean_dec(v_a_3911_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3939_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
if (lean_obj_tag(v_fst_3915_) == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_del_object(v___x_3913_);
v___x_3919_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3920_ = l_Lean_MessageData_ofName(v___x_3904_);
lean_inc_ref(v___x_3920_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set_tag(v___x_3917_, 7);
lean_ctor_set(v___x_3917_, 1, v___x_3920_);
lean_ctor_set(v___x_3917_, 0, v___x_3919_);
v___x_3922_ = v___x_3917_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3923_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3926_ = l_Lean_indentD(v___x_3925_);
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3924_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
lean_ctor_set(v___x_3930_, 1, v___x_3920_);
v___x_3931_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3932_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_3933_;
}
}
else
{
lean_object* v_val_3935_; lean_object* v___x_3937_; 
lean_del_object(v___x_3917_);
lean_dec(v___x_3904_);
lean_dec(v_stx_2365_);
v_val_3935_ = lean_ctor_get(v_fst_3915_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v_fst_3915_, 1);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v_val_3935_);
v___x_3937_ = v___x_3913_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_val_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v___x_3904_);
lean_dec(v_stx_2365_);
v_a_3942_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3910_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3910_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_dec(v_stx_2365_);
v___x_3950_ = lean_unsigned_to_nat(1u);
v___x_3951_ = l_Lean_Syntax_getArg(v___x_3900_, v___x_3950_);
lean_dec(v___x_3900_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3951_);
v___x_3953_ = v___x_3871_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
v_elseSeq_x3f_3876_ = v___x_3953_;
v___y_3877_ = v_a_2366_;
v___y_3878_ = v_a_2367_;
v___y_3879_ = v_a_2368_;
v___y_3880_ = v_a_2369_;
v___y_3881_ = v_a_2370_;
v___y_3882_ = v_a_2371_;
goto v___jp_3875_;
}
}
}
else
{
lean_object* v___x_3955_; 
lean_dec(v___x_3900_);
lean_del_object(v___x_3871_);
lean_dec(v_stx_2365_);
v___x_3955_ = lean_box(0);
v_elseSeq_x3f_3876_ = v___x_3955_;
v___y_3877_ = v_a_2366_;
v___y_3878_ = v_a_2367_;
v___y_3879_ = v_a_2368_;
v___y_3880_ = v_a_2369_;
v___y_3881_ = v_a_2370_;
v___y_3882_ = v_a_2371_;
goto v___jp_3875_;
}
v___jp_3875_:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; size_t v_sz_3886_; lean_object* v___x_3887_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = l_Array_reverse___redArg(v_val_3869_);
v_sz_3886_ = lean_array_size(v___x_3885_);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3885_, v_sz_3886_, v___x_3821_, v_a_3884_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec_ref(v___x_3885_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3874_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3898_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3898_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3898_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3890_, v_a_3888_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3894_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
else
{
lean_dec(v_a_3888_);
return v___x_3889_;
}
}
else
{
lean_dec(v___x_3874_);
return v___x_3887_;
}
}
else
{
lean_dec(v___x_3874_);
lean_dec(v_val_3869_);
return v___x_3883_;
}
}
}
}
}
}
else
{
lean_object* v___x_3957_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___x_4021_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_4021_ = lean_unsigned_to_nat(1u);
v___x_4128_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4021_);
v___x_4129_ = l_Lean_Syntax_isNone(v___x_4128_);
if (v___x_4129_ == 0)
{
uint8_t v___x_4130_; 
lean_inc(v___x_4128_);
v___x_4130_ = l_Lean_Syntax_matchesNull(v___x_4128_, v___x_4021_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_env_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec(v___x_4128_);
lean_inc_n(v_stx_2365_, 2);
v___x_4131_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4132_ = lean_st_ref_get(v_a_2371_);
v_env_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc_ref(v_env_4133_);
lean_dec(v___x_4132_);
v___x_4134_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4135_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4134_, v_env_4133_, v___x_4131_);
v___x_4136_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4137_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4135_, v___x_4136_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4135_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4168_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4168_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4168_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_fst_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4166_; 
v_fst_4142_ = lean_ctor_get(v_a_4138_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_a_4138_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; 
v_unused_4167_ = lean_ctor_get(v_a_4138_, 1);
lean_dec(v_unused_4167_);
v___x_4144_ = v_a_4138_;
v_isShared_4145_ = v_isSharedCheck_4166_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_fst_4142_);
lean_dec(v_a_4138_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4166_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
if (lean_obj_tag(v_fst_4142_) == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4149_; 
lean_del_object(v___x_4140_);
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4147_ = l_Lean_MessageData_ofName(v___x_4131_);
lean_inc_ref(v___x_4147_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set_tag(v___x_4144_, 7);
lean_ctor_set(v___x_4144_, 1, v___x_4147_);
lean_ctor_set(v___x_4144_, 0, v___x_4146_);
v___x_4149_ = v___x_4144_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4150_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4153_ = l_Lean_indentD(v___x_4152_);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4151_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
lean_ctor_set(v___x_4157_, 1, v___x_4147_);
v___x_4158_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4159_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4160_;
}
}
else
{
lean_object* v_val_4162_; lean_object* v___x_4164_; 
lean_del_object(v___x_4144_);
lean_dec(v___x_4131_);
lean_dec(v_stx_2365_);
v_val_4162_ = lean_ctor_get(v_fst_4142_, 0);
lean_inc(v_val_4162_);
lean_dec_ref_known(v_fst_4142_, 1);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v_val_4162_);
v___x_4164_ = v___x_4140_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_val_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v___x_4131_);
lean_dec(v_stx_2365_);
v_a_4169_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4137_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4137_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v___x_4177_ = l_Lean_Syntax_getArg(v___x_4128_, v___x_3957_);
lean_dec(v___x_4128_);
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4179_ = l_Lean_Syntax_isOfKind(v___x_4177_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v_env_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4180_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4181_ = lean_st_ref_get(v_a_2371_);
v_env_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc_ref(v_env_4182_);
lean_dec(v___x_4181_);
v___x_4183_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4184_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4183_, v_env_4182_, v___x_4180_);
v___x_4185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4186_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4184_, v___x_4185_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4184_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4217_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4217_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4217_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v_fst_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4215_; 
v_fst_4191_ = lean_ctor_get(v_a_4187_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_a_4187_);
if (v_isSharedCheck_4215_ == 0)
{
lean_object* v_unused_4216_; 
v_unused_4216_ = lean_ctor_get(v_a_4187_, 1);
lean_dec(v_unused_4216_);
v___x_4193_ = v_a_4187_;
v_isShared_4194_ = v_isSharedCheck_4215_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_fst_4191_);
lean_dec(v_a_4187_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4215_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
if (lean_obj_tag(v_fst_4191_) == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
lean_del_object(v___x_4189_);
v___x_4195_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4196_ = l_Lean_MessageData_ofName(v___x_4180_);
lean_inc_ref(v___x_4196_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 7);
lean_ctor_set(v___x_4193_, 1, v___x_4196_);
lean_ctor_set(v___x_4193_, 0, v___x_4195_);
v___x_4198_ = v___x_4193_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4210_, 1, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4199_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4198_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4202_ = l_Lean_indentD(v___x_4201_);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4200_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v___x_4196_);
v___x_4207_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4206_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4208_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4209_;
}
}
else
{
lean_object* v_val_4211_; lean_object* v___x_4213_; 
lean_del_object(v___x_4193_);
lean_dec(v___x_4180_);
lean_dec(v_stx_2365_);
v_val_4211_ = lean_ctor_get(v_fst_4191_, 0);
lean_inc(v_val_4211_);
lean_dec_ref_known(v_fst_4191_, 1);
if (v_isShared_4190_ == 0)
{
lean_ctor_set(v___x_4189_, 0, v_val_4211_);
v___x_4213_ = v___x_4189_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_val_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec(v___x_4180_);
lean_dec(v_stx_2365_);
v_a_4218_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4186_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4186_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
v___y_4023_ = v_a_2366_;
v___y_4024_ = v_a_2367_;
v___y_4025_ = v_a_2368_;
v___y_4026_ = v_a_2369_;
v___y_4027_ = v_a_2370_;
v___y_4028_ = v_a_2371_;
goto v___jp_4022_;
}
}
}
else
{
lean_dec(v___x_4128_);
v___y_4023_ = v_a_2366_;
v___y_4024_ = v_a_2367_;
v___y_4025_ = v_a_2368_;
v___y_4026_ = v_a_2369_;
v___y_4027_ = v_a_2370_;
v___y_4028_ = v_a_2371_;
goto v___jp_4022_;
}
v___jp_3958_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3965_ = lean_unsigned_to_nat(6u);
v___x_3966_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3966_);
v___x_3968_ = l_Lean_Syntax_isOfKind(v___x_3966_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_env_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec(v___x_3966_);
lean_inc_n(v_stx_2365_, 2);
v___x_3969_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_3970_ = lean_st_ref_get(v___y_3964_);
v_env_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_ref(v_env_3971_);
lean_dec(v___x_3970_);
v___x_3972_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3973_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3972_, v_env_3971_, v___x_3969_);
v___x_3974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3975_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_3973_, v___x_3974_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec(v___x_3973_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4006_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_4006_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4006_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_fst_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4004_; 
v_fst_3980_ = lean_ctor_get(v_a_3976_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_a_3976_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; 
v_unused_4005_ = lean_ctor_get(v_a_3976_, 1);
lean_dec(v_unused_4005_);
v___x_3982_ = v_a_3976_;
v_isShared_3983_ = v_isSharedCheck_4004_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_fst_3980_);
lean_dec(v_a_3976_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4004_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
if (lean_obj_tag(v_fst_3980_) == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_del_object(v___x_3978_);
v___x_3984_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3985_ = l_Lean_MessageData_ofName(v___x_3969_);
lean_inc_ref(v___x_3985_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set_tag(v___x_3982_, 7);
lean_ctor_set(v___x_3982_, 1, v___x_3985_);
lean_ctor_set(v___x_3982_, 0, v___x_3984_);
v___x_3987_ = v___x_3982_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3984_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3988_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3987_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_3991_ = l_Lean_indentD(v___x_3990_);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3989_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
lean_ctor_set(v___x_3995_, 1, v___x_3985_);
v___x_3996_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3997_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3998_;
}
}
else
{
lean_object* v_val_4000_; lean_object* v___x_4002_; 
lean_del_object(v___x_3982_);
lean_dec(v___x_3969_);
lean_dec(v_stx_2365_);
v_val_4000_ = lean_ctor_get(v_fst_3980_, 0);
lean_inc(v_val_4000_);
lean_dec_ref_known(v_fst_3980_, 1);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v_val_4000_);
v___x_4002_ = v___x_3978_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_val_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v___x_3969_);
lean_dec(v_stx_2365_);
v_a_4007_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3975_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3975_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; size_t v_sz_4018_; size_t v___x_4019_; lean_object* v___x_4020_; 
lean_dec(v_stx_2365_);
v___x_4015_ = l_Lean_Syntax_getArg(v___x_3966_, v___x_3957_);
lean_dec(v___x_3966_);
v___x_4016_ = l_Lean_Syntax_getArgs(v___x_4015_);
lean_dec(v___x_4015_);
v___x_4017_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4018_ = lean_array_size(v___x_4016_);
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2689_, v___x_4016_, v_sz_4018_, v___x_4019_, v___x_4017_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec_ref(v___x_4016_);
return v___x_4020_;
}
}
v___jp_4022_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4029_ = lean_unsigned_to_nat(2u);
v___x_4030_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4029_);
v___x_4031_ = l_Lean_Syntax_isNone(v___x_4030_);
if (v___x_4031_ == 0)
{
uint8_t v___x_4032_; 
lean_inc(v___x_4030_);
v___x_4032_ = l_Lean_Syntax_matchesNull(v___x_4030_, v___x_4021_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_env_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec(v___x_4030_);
lean_inc_n(v_stx_2365_, 2);
v___x_4033_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4034_ = lean_st_ref_get(v___y_4028_);
v_env_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc_ref(v_env_4035_);
lean_dec(v___x_4034_);
v___x_4036_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4037_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4036_, v_env_4035_, v___x_4033_);
v___x_4038_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4039_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4037_, v___x_4038_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___x_4037_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4070_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4042_ = v___x_4039_;
v_isShared_4043_ = v_isSharedCheck_4070_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4070_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v_fst_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4068_; 
v_fst_4044_ = lean_ctor_get(v_a_4040_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_a_4040_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; 
v_unused_4069_ = lean_ctor_get(v_a_4040_, 1);
lean_dec(v_unused_4069_);
v___x_4046_ = v_a_4040_;
v_isShared_4047_ = v_isSharedCheck_4068_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_fst_4044_);
lean_dec(v_a_4040_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4068_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
if (lean_obj_tag(v_fst_4044_) == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
lean_del_object(v___x_4042_);
v___x_4048_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4049_ = l_Lean_MessageData_ofName(v___x_4033_);
lean_inc_ref(v___x_4049_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 7);
lean_ctor_set(v___x_4046_, 1, v___x_4049_);
lean_ctor_set(v___x_4046_, 0, v___x_4048_);
v___x_4051_ = v___x_4046_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4052_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4055_ = l_Lean_indentD(v___x_4054_);
v___x_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4053_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v___x_4049_);
v___x_4060_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4061_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
return v___x_4062_;
}
}
else
{
lean_object* v_val_4064_; lean_object* v___x_4066_; 
lean_del_object(v___x_4046_);
lean_dec(v___x_4033_);
lean_dec(v_stx_2365_);
v_val_4064_ = lean_ctor_get(v_fst_4044_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_fst_4044_, 1);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v_val_4064_);
v___x_4066_ = v___x_4042_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_val_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v___x_4033_);
lean_dec(v_stx_2365_);
v_a_4071_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4039_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4039_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4079_ = l_Lean_Syntax_getArg(v___x_4030_, v___x_3957_);
lean_dec(v___x_4030_);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4081_ = l_Lean_Syntax_isOfKind(v___x_4079_, v___x_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v_env_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4082_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4083_ = lean_st_ref_get(v___y_4028_);
v_env_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_ref(v_env_4084_);
lean_dec(v___x_4083_);
v___x_4085_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4086_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4085_, v_env_4084_, v___x_4082_);
v___x_4087_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4088_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4086_, v___x_4087_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___x_4086_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4119_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4091_ = v___x_4088_;
v_isShared_4092_ = v_isSharedCheck_4119_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4088_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4119_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v_fst_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4117_; 
v_fst_4093_ = lean_ctor_get(v_a_4089_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_a_4089_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; 
v_unused_4118_ = lean_ctor_get(v_a_4089_, 1);
lean_dec(v_unused_4118_);
v___x_4095_ = v_a_4089_;
v_isShared_4096_ = v_isSharedCheck_4117_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_fst_4093_);
lean_dec(v_a_4089_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4117_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
if (lean_obj_tag(v_fst_4093_) == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
lean_del_object(v___x_4091_);
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4098_ = l_Lean_MessageData_ofName(v___x_4082_);
lean_inc_ref(v___x_4098_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set_tag(v___x_4095_, 7);
lean_ctor_set(v___x_4095_, 1, v___x_4098_);
lean_ctor_set(v___x_4095_, 0, v___x_4097_);
v___x_4100_ = v___x_4095_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4101_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4104_ = l_Lean_indentD(v___x_4103_);
v___x_4105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4102_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set(v___x_4108_, 1, v___x_4098_);
v___x_4109_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4110_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
return v___x_4111_;
}
}
else
{
lean_object* v_val_4113_; lean_object* v___x_4115_; 
lean_del_object(v___x_4095_);
lean_dec(v___x_4082_);
lean_dec(v_stx_2365_);
v_val_4113_ = lean_ctor_get(v_fst_4093_, 0);
lean_inc(v_val_4113_);
lean_dec_ref_known(v_fst_4093_, 1);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 0, v_val_4113_);
v___x_4115_ = v___x_4091_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_val_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v___x_4082_);
lean_dec(v_stx_2365_);
v_a_4120_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4088_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4088_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
v___y_3959_ = v___y_4023_;
v___y_3960_ = v___y_4024_;
v___y_3961_ = v___y_4025_;
v___y_3962_ = v___y_4026_;
v___y_3963_ = v___y_4027_;
v___y_3964_ = v___y_4028_;
goto v___jp_3958_;
}
}
}
else
{
lean_dec(v___x_4030_);
v___y_3959_ = v___y_4023_;
v___y_3960_ = v___y_4024_;
v___y_3961_ = v___y_4025_;
v___y_3962_ = v___y_4026_;
v___y_3963_ = v___y_4027_;
v___y_3964_ = v___y_4028_;
goto v___jp_3958_;
}
}
}
}
else
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4226_);
v___x_4228_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4227_);
v___x_4229_ = l_Lean_Syntax_isOfKind(v___x_4227_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4227_);
v___x_4231_ = l_Lean_Syntax_isOfKind(v___x_4227_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v_env_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec(v___x_4227_);
lean_inc_n(v_stx_2365_, 2);
v___x_4232_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4233_ = lean_st_ref_get(v_a_2371_);
v_env_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc_ref(v_env_4234_);
lean_dec(v___x_4233_);
v___x_4235_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4236_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4235_, v_env_4234_, v___x_4232_);
v___x_4237_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4238_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4236_, v___x_4237_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4236_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4269_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4269_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4269_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v_fst_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4267_; 
v_fst_4243_ = lean_ctor_get(v_a_4239_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_a_4239_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; 
v_unused_4268_ = lean_ctor_get(v_a_4239_, 1);
lean_dec(v_unused_4268_);
v___x_4245_ = v_a_4239_;
v_isShared_4246_ = v_isSharedCheck_4267_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_fst_4243_);
lean_dec(v_a_4239_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4267_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
if (lean_obj_tag(v_fst_4243_) == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
lean_del_object(v___x_4241_);
v___x_4247_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4248_ = l_Lean_MessageData_ofName(v___x_4232_);
lean_inc_ref(v___x_4248_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 7);
lean_ctor_set(v___x_4245_, 1, v___x_4248_);
lean_ctor_set(v___x_4245_, 0, v___x_4247_);
v___x_4250_ = v___x_4245_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4251_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4254_ = l_Lean_indentD(v___x_4253_);
v___x_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4252_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
lean_ctor_set(v___x_4258_, 1, v___x_4248_);
v___x_4259_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4260_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4261_;
}
}
else
{
lean_object* v_val_4263_; lean_object* v___x_4265_; 
lean_del_object(v___x_4245_);
lean_dec(v___x_4232_);
lean_dec(v_stx_2365_);
v_val_4263_ = lean_ctor_get(v_fst_4243_, 0);
lean_inc(v_val_4263_);
lean_dec_ref_known(v_fst_4243_, 1);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v_val_4263_);
v___x_4265_ = v___x_4241_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_val_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v___x_4232_);
lean_dec(v_stx_2365_);
v_a_4270_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4238_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4238_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_stx_2365_);
v___x_4278_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2605_, v___x_4227_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4278_;
}
}
else
{
lean_object* v___x_4279_; 
lean_dec(v_stx_2365_);
v___x_4279_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2605_, v___x_4227_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4279_;
}
}
}
else
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4280_ = lean_unsigned_to_nat(0u);
v___x_4281_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4280_);
v___x_4282_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4281_);
v___x_4283_ = l_Lean_Syntax_isOfKind(v___x_4281_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4284_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4281_);
v___x_4285_ = l_Lean_Syntax_isOfKind(v___x_4281_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_env_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
lean_dec(v___x_4281_);
lean_inc_n(v_stx_2365_, 2);
v___x_4286_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4287_ = lean_st_ref_get(v_a_2371_);
v_env_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc_ref(v_env_4288_);
lean_dec(v___x_4287_);
v___x_4289_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4290_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4289_, v_env_4288_, v___x_4286_);
v___x_4291_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4292_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4290_, v___x_4291_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4290_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4323_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4323_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4323_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_fst_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4321_; 
v_fst_4297_ = lean_ctor_get(v_a_4293_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_a_4293_);
if (v_isSharedCheck_4321_ == 0)
{
lean_object* v_unused_4322_; 
v_unused_4322_ = lean_ctor_get(v_a_4293_, 1);
lean_dec(v_unused_4322_);
v___x_4299_ = v_a_4293_;
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_fst_4297_);
lean_dec(v_a_4293_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
if (lean_obj_tag(v_fst_4297_) == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
lean_del_object(v___x_4295_);
v___x_4301_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4302_ = l_Lean_MessageData_ofName(v___x_4286_);
lean_inc_ref(v___x_4302_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 7);
lean_ctor_set(v___x_4299_, 1, v___x_4302_);
lean_ctor_set(v___x_4299_, 0, v___x_4301_);
v___x_4304_ = v___x_4299_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4305_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4308_ = l_Lean_indentD(v___x_4307_);
v___x_4309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4306_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
lean_ctor_set(v___x_4312_, 1, v___x_4302_);
v___x_4313_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4314_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4315_;
}
}
else
{
lean_object* v_val_4317_; lean_object* v___x_4319_; 
lean_del_object(v___x_4299_);
lean_dec(v___x_4286_);
lean_dec(v_stx_2365_);
v_val_4317_ = lean_ctor_get(v_fst_4297_, 0);
lean_inc(v_val_4317_);
lean_dec_ref_known(v_fst_4297_, 1);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v_val_4317_);
v___x_4319_ = v___x_4295_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_val_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec(v___x_4286_);
lean_dec(v_stx_2365_);
v_a_4324_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4292_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4292_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v___x_4332_; 
lean_dec(v_stx_2365_);
v___x_4332_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4281_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4281_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
v___x_4334_ = lean_box(0);
v___x_4335_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4333_, v___x_4334_, v___x_4334_, v___x_4334_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4335_;
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
v_a_4336_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4332_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4332_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
else
{
lean_object* v___x_4344_; 
lean_dec(v_stx_2365_);
v___x_4344_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4281_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4281_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = lean_box(0);
v___x_4347_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4345_, v___x_4346_, v___x_4346_, v___x_4346_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4347_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4344_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4344_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4356_);
v___x_4358_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4357_);
v___x_4359_ = l_Lean_Syntax_isOfKind(v___x_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v_env_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
lean_dec(v___x_4357_);
lean_inc_n(v_stx_2365_, 2);
v___x_4360_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4361_ = lean_st_ref_get(v_a_2371_);
v_env_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc_ref(v_env_4362_);
lean_dec(v___x_4361_);
v___x_4363_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4364_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4363_, v_env_4362_, v___x_4360_);
v___x_4365_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4366_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4364_, v___x_4365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4364_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4397_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4397_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4397_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_fst_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4395_; 
v_fst_4371_ = lean_ctor_get(v_a_4367_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v_a_4367_);
if (v_isSharedCheck_4395_ == 0)
{
lean_object* v_unused_4396_; 
v_unused_4396_ = lean_ctor_get(v_a_4367_, 1);
lean_dec(v_unused_4396_);
v___x_4373_ = v_a_4367_;
v_isShared_4374_ = v_isSharedCheck_4395_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_fst_4371_);
lean_dec(v_a_4367_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4395_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
if (lean_obj_tag(v_fst_4371_) == 0)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
lean_del_object(v___x_4369_);
v___x_4375_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4376_ = l_Lean_MessageData_ofName(v___x_4360_);
lean_inc_ref(v___x_4376_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set_tag(v___x_4373_, 7);
lean_ctor_set(v___x_4373_, 1, v___x_4376_);
lean_ctor_set(v___x_4373_, 0, v___x_4375_);
v___x_4378_ = v___x_4373_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4375_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4378_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4382_ = l_Lean_indentD(v___x_4381_);
v___x_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
lean_ctor_set(v___x_4386_, 1, v___x_4376_);
v___x_4387_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4388_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4389_;
}
}
else
{
lean_object* v_val_4391_; lean_object* v___x_4393_; 
lean_del_object(v___x_4373_);
lean_dec(v___x_4360_);
lean_dec(v_stx_2365_);
v_val_4391_ = lean_ctor_get(v_fst_4371_, 0);
lean_inc(v_val_4391_);
lean_dec_ref_known(v_fst_4371_, 1);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v_val_4391_);
v___x_4393_ = v___x_4369_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_val_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v___x_4360_);
lean_dec(v_stx_2365_);
v_a_4398_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4366_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4366_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
else
{
lean_object* v___x_4406_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4406_ = lean_unsigned_to_nat(1u);
v___x_4512_ = l_Lean_Syntax_getArg(v___x_4357_, v___x_4406_);
lean_dec(v___x_4357_);
v___x_4513_ = l_Lean_Syntax_isNone(v___x_4512_);
if (v___x_4513_ == 0)
{
uint8_t v___x_4514_; 
v___x_4514_ = l_Lean_Syntax_matchesNull(v___x_4512_, v___x_4406_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v_env_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4515_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4516_ = lean_st_ref_get(v_a_2371_);
v_env_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc_ref(v_env_4517_);
lean_dec(v___x_4516_);
v___x_4518_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4519_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4518_, v_env_4517_, v___x_4515_);
v___x_4520_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4521_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4519_, v___x_4520_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4519_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4552_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4524_ = v___x_4521_;
v_isShared_4525_ = v_isSharedCheck_4552_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4552_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v_fst_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4550_; 
v_fst_4526_ = lean_ctor_get(v_a_4522_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_a_4522_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v_a_4522_, 1);
lean_dec(v_unused_4551_);
v___x_4528_ = v_a_4522_;
v_isShared_4529_ = v_isSharedCheck_4550_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_fst_4526_);
lean_dec(v_a_4522_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4550_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
if (lean_obj_tag(v_fst_4526_) == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
lean_del_object(v___x_4524_);
v___x_4530_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4531_ = l_Lean_MessageData_ofName(v___x_4515_);
lean_inc_ref(v___x_4531_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set_tag(v___x_4528_, 7);
lean_ctor_set(v___x_4528_, 1, v___x_4531_);
lean_ctor_set(v___x_4528_, 0, v___x_4530_);
v___x_4533_ = v___x_4528_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4534_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4537_ = l_Lean_indentD(v___x_4536_);
v___x_4538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4535_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
lean_ctor_set(v___x_4541_, 1, v___x_4531_);
v___x_4542_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
v___x_4544_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4543_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4544_;
}
}
else
{
lean_object* v_val_4546_; lean_object* v___x_4548_; 
lean_del_object(v___x_4528_);
lean_dec(v___x_4515_);
lean_dec(v_stx_2365_);
v_val_4546_ = lean_ctor_get(v_fst_4526_, 0);
lean_inc(v_val_4546_);
lean_dec_ref_known(v_fst_4526_, 1);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v_val_4546_);
v___x_4548_ = v___x_4524_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_val_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v___x_4515_);
lean_dec(v_stx_2365_);
v_a_4553_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4521_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4521_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
else
{
v___y_4408_ = v_a_2366_;
v___y_4409_ = v_a_2367_;
v___y_4410_ = v_a_2368_;
v___y_4411_ = v_a_2369_;
v___y_4412_ = v_a_2370_;
v___y_4413_ = v_a_2371_;
goto v___jp_4407_;
}
}
else
{
lean_dec(v___x_4512_);
v___y_4408_ = v_a_2366_;
v___y_4409_ = v_a_2367_;
v___y_4410_ = v_a_2368_;
v___y_4411_ = v_a_2369_;
v___y_4412_ = v_a_2370_;
v___y_4413_ = v_a_2371_;
goto v___jp_4407_;
}
v___jp_4407_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4414_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4406_);
v___x_4415_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4414_);
v___x_4416_ = l_Lean_Syntax_isOfKind(v___x_4414_, v___x_4415_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v_env_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec(v___x_4414_);
lean_inc_n(v_stx_2365_, 2);
v___x_4417_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4418_ = lean_st_ref_get(v___y_4413_);
v_env_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc_ref(v_env_4419_);
lean_dec(v___x_4418_);
v___x_4420_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4421_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4420_, v_env_4419_, v___x_4417_);
v___x_4422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4423_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4421_, v___x_4422_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___x_4421_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4454_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4454_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4454_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v_fst_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4452_; 
v_fst_4428_ = lean_ctor_get(v_a_4424_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_a_4424_);
if (v_isSharedCheck_4452_ == 0)
{
lean_object* v_unused_4453_; 
v_unused_4453_ = lean_ctor_get(v_a_4424_, 1);
lean_dec(v_unused_4453_);
v___x_4430_ = v_a_4424_;
v_isShared_4431_ = v_isSharedCheck_4452_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_fst_4428_);
lean_dec(v_a_4424_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4452_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
if (lean_obj_tag(v_fst_4428_) == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4435_; 
lean_del_object(v___x_4426_);
v___x_4432_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4433_ = l_Lean_MessageData_ofName(v___x_4417_);
lean_inc_ref(v___x_4433_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set_tag(v___x_4430_, 7);
lean_ctor_set(v___x_4430_, 1, v___x_4433_);
lean_ctor_set(v___x_4430_, 0, v___x_4432_);
v___x_4435_ = v___x_4430_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4439_ = l_Lean_indentD(v___x_4438_);
v___x_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4437_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
v___x_4441_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4440_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
lean_ctor_set(v___x_4443_, 1, v___x_4433_);
v___x_4444_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4443_);
lean_ctor_set(v___x_4445_, 1, v___x_4444_);
v___x_4446_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4445_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4446_;
}
}
else
{
lean_object* v_val_4448_; lean_object* v___x_4450_; 
lean_del_object(v___x_4430_);
lean_dec(v___x_4417_);
lean_dec(v_stx_2365_);
v_val_4448_ = lean_ctor_get(v_fst_4428_, 0);
lean_inc(v_val_4448_);
lean_dec_ref_known(v_fst_4428_, 1);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v_val_4448_);
v___x_4450_ = v___x_4426_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_val_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec(v___x_4417_);
lean_dec(v_stx_2365_);
v_a_4455_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4423_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4423_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
else
{
lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4463_ = l_Lean_Syntax_getArg(v___x_4414_, v___x_4406_);
lean_dec(v___x_4414_);
v___x_4464_ = l_Lean_Syntax_isNone(v___x_4463_);
if (v___x_4464_ == 0)
{
uint8_t v___x_4465_; 
v___x_4465_ = l_Lean_Syntax_matchesNull(v___x_4463_, v___x_4406_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v_env_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4466_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4467_ = lean_st_ref_get(v___y_4413_);
v_env_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc_ref(v_env_4468_);
lean_dec(v___x_4467_);
v___x_4469_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4470_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4469_, v_env_4468_, v___x_4466_);
v___x_4471_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4472_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4470_, v___x_4471_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___x_4470_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4503_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4503_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4503_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_fst_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4501_; 
v_fst_4477_ = lean_ctor_get(v_a_4473_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_a_4473_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v_a_4473_, 1);
lean_dec(v_unused_4502_);
v___x_4479_ = v_a_4473_;
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_fst_4477_);
lean_dec(v_a_4473_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
if (lean_obj_tag(v_fst_4477_) == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
lean_del_object(v___x_4475_);
v___x_4481_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4482_ = l_Lean_MessageData_ofName(v___x_4466_);
lean_inc_ref(v___x_4482_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set_tag(v___x_4479_, 7);
lean_ctor_set(v___x_4479_, 1, v___x_4482_);
lean_ctor_set(v___x_4479_, 0, v___x_4481_);
v___x_4484_ = v___x_4479_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4485_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4484_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4488_ = l_Lean_indentD(v___x_4487_);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4486_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___x_4482_);
v___x_4493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4494_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4495_;
}
}
else
{
lean_object* v_val_4497_; lean_object* v___x_4499_; 
lean_del_object(v___x_4479_);
lean_dec(v___x_4466_);
lean_dec(v_stx_2365_);
v_val_4497_ = lean_ctor_get(v_fst_4477_, 0);
lean_inc(v_val_4497_);
lean_dec_ref_known(v_fst_4477_, 1);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v_val_4497_);
v___x_4499_ = v___x_4475_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_val_4497_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v___x_4466_);
lean_dec(v_stx_2365_);
v_a_4504_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4472_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4472_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_dec(v_stx_2365_);
goto v___jp_2391_;
}
}
else
{
lean_dec(v___x_4463_);
lean_dec(v_stx_2365_);
goto v___jp_2391_;
}
}
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4561_);
v___x_4563_ = l_Lean_Syntax_isNone(v___x_4562_);
if (v___x_4563_ == 0)
{
uint8_t v___x_4564_; 
v___x_4564_ = l_Lean_Syntax_matchesNull(v___x_4562_, v___x_4561_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v_env_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4565_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4566_ = lean_st_ref_get(v_a_2371_);
v_env_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc_ref(v_env_4567_);
lean_dec(v___x_4566_);
v___x_4568_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4569_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4568_, v_env_4567_, v___x_4565_);
v___x_4570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4571_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4569_, v___x_4570_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4569_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4602_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4602_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4602_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v_fst_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4600_; 
v_fst_4576_ = lean_ctor_get(v_a_4572_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_a_4572_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v_a_4572_, 1);
lean_dec(v_unused_4601_);
v___x_4578_ = v_a_4572_;
v_isShared_4579_ = v_isSharedCheck_4600_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_fst_4576_);
lean_dec(v_a_4572_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4600_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
if (lean_obj_tag(v_fst_4576_) == 0)
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
lean_del_object(v___x_4574_);
v___x_4580_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4581_ = l_Lean_MessageData_ofName(v___x_4565_);
lean_inc_ref(v___x_4581_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set_tag(v___x_4578_, 7);
lean_ctor_set(v___x_4578_, 1, v___x_4581_);
lean_ctor_set(v___x_4578_, 0, v___x_4580_);
v___x_4583_ = v___x_4578_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4584_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4587_ = l_Lean_indentD(v___x_4586_);
v___x_4588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4585_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4588_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
lean_ctor_set(v___x_4591_, 1, v___x_4581_);
v___x_4592_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4593_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4594_;
}
}
else
{
lean_object* v_val_4596_; lean_object* v___x_4598_; 
lean_del_object(v___x_4578_);
lean_dec(v___x_4565_);
lean_dec(v_stx_2365_);
v_val_4596_ = lean_ctor_get(v_fst_4576_, 0);
lean_inc(v_val_4596_);
lean_dec_ref_known(v_fst_4576_, 1);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v_val_4596_);
v___x_4598_ = v___x_4574_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_val_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec(v___x_4565_);
lean_dec(v_stx_2365_);
v_a_4603_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4571_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4571_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
v___y_2623_ = v_a_2366_;
v___y_2624_ = v_a_2367_;
v___y_2625_ = v_a_2368_;
v___y_2626_ = v_a_2369_;
v___y_2627_ = v_a_2370_;
v___y_2628_ = v_a_2371_;
goto v___jp_2622_;
}
}
else
{
lean_dec(v___x_4562_);
v___y_2623_ = v_a_2366_;
v___y_2624_ = v_a_2367_;
v___y_2625_ = v_a_2368_;
v___y_2626_ = v_a_2369_;
v___y_2627_ = v_a_2370_;
v___y_2628_ = v_a_2371_;
goto v___jp_2622_;
}
}
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; uint8_t v___x_4613_; 
v___x_4611_ = lean_unsigned_to_nat(1u);
v___x_4612_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4611_);
v___x_4613_ = l_Lean_Syntax_isNone(v___x_4612_);
if (v___x_4613_ == 0)
{
uint8_t v___x_4614_; 
v___x_4614_ = l_Lean_Syntax_matchesNull(v___x_4612_, v___x_4611_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v_env_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4615_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4616_ = lean_st_ref_get(v_a_2371_);
v_env_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc_ref(v_env_4617_);
lean_dec(v___x_4616_);
v___x_4618_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4619_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4618_, v_env_4617_, v___x_4615_);
v___x_4620_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4621_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4619_, v___x_4620_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4619_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4652_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4652_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4652_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v_fst_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4650_; 
v_fst_4626_ = lean_ctor_get(v_a_4622_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_a_4622_);
if (v_isSharedCheck_4650_ == 0)
{
lean_object* v_unused_4651_; 
v_unused_4651_ = lean_ctor_get(v_a_4622_, 1);
lean_dec(v_unused_4651_);
v___x_4628_ = v_a_4622_;
v_isShared_4629_ = v_isSharedCheck_4650_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_fst_4626_);
lean_dec(v_a_4622_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4650_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
if (lean_obj_tag(v_fst_4626_) == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
lean_del_object(v___x_4624_);
v___x_4630_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4631_ = l_Lean_MessageData_ofName(v___x_4615_);
lean_inc_ref(v___x_4631_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set_tag(v___x_4628_, 7);
lean_ctor_set(v___x_4628_, 1, v___x_4631_);
lean_ctor_set(v___x_4628_, 0, v___x_4630_);
v___x_4633_ = v___x_4628_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4633_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
v___x_4636_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4637_ = l_Lean_indentD(v___x_4636_);
v___x_4638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4635_);
lean_ctor_set(v___x_4638_, 1, v___x_4637_);
v___x_4639_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4638_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
v___x_4641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4640_);
lean_ctor_set(v___x_4641_, 1, v___x_4631_);
v___x_4642_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4641_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
v___x_4644_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4643_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4644_;
}
}
else
{
lean_object* v_val_4646_; lean_object* v___x_4648_; 
lean_del_object(v___x_4628_);
lean_dec(v___x_4615_);
lean_dec(v_stx_2365_);
v_val_4646_ = lean_ctor_get(v_fst_4626_, 0);
lean_inc(v_val_4646_);
lean_dec_ref_known(v_fst_4626_, 1);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v_val_4646_);
v___x_4648_ = v___x_4624_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_val_4646_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec(v___x_4615_);
lean_dec(v_stx_2365_);
v_a_4653_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4621_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4621_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
else
{
v___y_2422_ = v_a_2366_;
v___y_2423_ = v_a_2367_;
v___y_2424_ = v_a_2368_;
v___y_2425_ = v_a_2369_;
v___y_2426_ = v_a_2370_;
v___y_2427_ = v_a_2371_;
goto v___jp_2421_;
}
}
else
{
lean_dec(v___x_4612_);
v___y_2422_ = v_a_2366_;
v___y_2423_ = v_a_2367_;
v___y_2424_ = v_a_2368_;
v___y_2425_ = v_a_2369_;
v___y_2426_ = v_a_2370_;
v___y_2427_ = v_a_2371_;
goto v___jp_2421_;
}
}
v___jp_2622_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2629_);
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2632_ = l_Lean_Syntax_isOfKind(v___x_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v_env_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_inc_n(v_stx_2365_, 2);
v___x_2633_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2634_ = lean_st_ref_get(v___y_2628_);
v_env_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_env_2635_);
lean_dec(v___x_2634_);
v___x_2636_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2637_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2636_, v_env_2635_, v___x_2633_);
v___x_2638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2639_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2637_, v___x_2638_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___x_2637_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2670_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2670_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2670_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_fst_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2668_; 
v_fst_2644_ = lean_ctor_get(v_a_2640_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v_a_2640_, 1);
lean_dec(v_unused_2669_);
v___x_2646_ = v_a_2640_;
v_isShared_2647_ = v_isSharedCheck_2668_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_fst_2644_);
lean_dec(v_a_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2668_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
if (lean_obj_tag(v_fst_2644_) == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_del_object(v___x_2642_);
v___x_2648_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2649_ = l_Lean_MessageData_ofName(v___x_2633_);
lean_inc_ref(v___x_2649_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 7);
lean_ctor_set(v___x_2646_, 1, v___x_2649_);
lean_ctor_set(v___x_2646_, 0, v___x_2648_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2652_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2655_ = l_Lean_indentD(v___x_2654_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2649_);
v___x_2660_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2661_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2662_;
}
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; 
lean_del_object(v___x_2646_);
lean_dec(v___x_2633_);
lean_dec(v_stx_2365_);
v_val_2664_ = lean_ctor_get(v_fst_2644_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_fst_2644_, 1);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_val_2664_);
v___x_2666_ = v___x_2642_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_val_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v___x_2633_);
lean_dec(v_stx_2365_);
v_a_2671_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2639_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2639_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_unsigned_to_nat(3u);
v___x_2680_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2679_);
lean_dec(v_stx_2365_);
v___x_2681_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2621_, v___x_2680_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2681_;
}
}
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4661_);
v___x_4663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4664_ = l_Lean_Syntax_isOfKind(v___x_4662_, v___x_4663_);
if (v___x_4664_ == 0)
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v_env_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4665_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4666_ = lean_st_ref_get(v_a_2371_);
v_env_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc_ref(v_env_4667_);
lean_dec(v___x_4666_);
v___x_4668_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4669_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4668_, v_env_4667_, v___x_4665_);
v___x_4670_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4671_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4669_, v___x_4670_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4669_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4702_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4702_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4702_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_fst_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4700_; 
v_fst_4676_ = lean_ctor_get(v_a_4672_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v_a_4672_);
if (v_isSharedCheck_4700_ == 0)
{
lean_object* v_unused_4701_; 
v_unused_4701_ = lean_ctor_get(v_a_4672_, 1);
lean_dec(v_unused_4701_);
v___x_4678_ = v_a_4672_;
v_isShared_4679_ = v_isSharedCheck_4700_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_fst_4676_);
lean_dec(v_a_4672_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4700_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
if (lean_obj_tag(v_fst_4676_) == 0)
{
lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4683_; 
lean_del_object(v___x_4674_);
v___x_4680_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4681_ = l_Lean_MessageData_ofName(v___x_4665_);
lean_inc_ref(v___x_4681_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 7);
lean_ctor_set(v___x_4678_, 1, v___x_4681_);
lean_ctor_set(v___x_4678_, 0, v___x_4680_);
v___x_4683_ = v___x_4678_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4684_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4683_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
v___x_4686_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4687_ = l_Lean_indentD(v___x_4686_);
v___x_4688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4685_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4688_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
v___x_4691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
lean_ctor_set(v___x_4691_, 1, v___x_4681_);
v___x_4692_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4691_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
v___x_4694_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4693_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4694_;
}
}
else
{
lean_object* v_val_4696_; lean_object* v___x_4698_; 
lean_del_object(v___x_4678_);
lean_dec(v___x_4665_);
lean_dec(v_stx_2365_);
v_val_4696_ = lean_ctor_get(v_fst_4676_, 0);
lean_inc(v_val_4696_);
lean_dec_ref_known(v_fst_4676_, 1);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v_val_4696_);
v___x_4698_ = v___x_4674_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_val_4696_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v___x_4665_);
lean_dec(v_stx_2365_);
v_a_4703_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4671_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4671_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4711_ = lean_unsigned_to_nat(1u);
v___x_4712_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4711_);
v___x_4713_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4712_);
v___x_4714_ = l_Lean_Syntax_isOfKind(v___x_4712_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v_env_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_dec(v___x_4712_);
lean_inc_n(v_stx_2365_, 2);
v___x_4715_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4716_ = lean_st_ref_get(v_a_2371_);
v_env_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc_ref(v_env_4717_);
lean_dec(v___x_4716_);
v___x_4718_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4719_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4718_, v_env_4717_, v___x_4715_);
v___x_4720_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4721_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4719_, v___x_4720_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4719_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4752_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4752_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4752_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v_fst_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4750_; 
v_fst_4726_ = lean_ctor_get(v_a_4722_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_a_4722_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v_a_4722_, 1);
lean_dec(v_unused_4751_);
v___x_4728_ = v_a_4722_;
v_isShared_4729_ = v_isSharedCheck_4750_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_fst_4726_);
lean_dec(v_a_4722_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4750_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
if (lean_obj_tag(v_fst_4726_) == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
lean_del_object(v___x_4724_);
v___x_4730_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4731_ = l_Lean_MessageData_ofName(v___x_4715_);
lean_inc_ref(v___x_4731_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set_tag(v___x_4728_, 7);
lean_ctor_set(v___x_4728_, 1, v___x_4731_);
lean_ctor_set(v___x_4728_, 0, v___x_4730_);
v___x_4733_ = v___x_4728_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4734_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4733_);
lean_ctor_set(v___x_4735_, 1, v___x_4734_);
v___x_4736_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4737_ = l_Lean_indentD(v___x_4736_);
v___x_4738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4735_);
lean_ctor_set(v___x_4738_, 1, v___x_4737_);
v___x_4739_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4738_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set(v___x_4741_, 1, v___x_4731_);
v___x_4742_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4743_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4744_;
}
}
else
{
lean_object* v_val_4746_; lean_object* v___x_4748_; 
lean_del_object(v___x_4728_);
lean_dec(v___x_4715_);
lean_dec(v_stx_2365_);
v_val_4746_ = lean_ctor_get(v_fst_4726_, 0);
lean_inc(v_val_4746_);
lean_dec_ref_known(v_fst_4726_, 1);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v_val_4746_);
v___x_4748_ = v___x_4724_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_val_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v___x_4715_);
lean_dec(v_stx_2365_);
v_a_4753_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4721_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4721_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = l_Lean_Syntax_getArg(v___x_4712_, v___x_4661_);
lean_dec(v___x_4712_);
lean_inc(v___x_4761_);
v___x_4762_ = l_Lean_Syntax_matchesNull(v___x_4761_, v___x_4711_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v_env_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec(v___x_4761_);
lean_inc_n(v_stx_2365_, 2);
v___x_4763_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4764_ = lean_st_ref_get(v_a_2371_);
v_env_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc_ref(v_env_4765_);
lean_dec(v___x_4764_);
v___x_4766_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4767_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4766_, v_env_4765_, v___x_4763_);
v___x_4768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4769_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4767_, v___x_4768_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4767_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4800_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4800_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4800_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v_fst_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4798_; 
v_fst_4774_ = lean_ctor_get(v_a_4770_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_a_4770_);
if (v_isSharedCheck_4798_ == 0)
{
lean_object* v_unused_4799_; 
v_unused_4799_ = lean_ctor_get(v_a_4770_, 1);
lean_dec(v_unused_4799_);
v___x_4776_ = v_a_4770_;
v_isShared_4777_ = v_isSharedCheck_4798_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_fst_4774_);
lean_dec(v_a_4770_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4798_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
if (lean_obj_tag(v_fst_4774_) == 0)
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4781_; 
lean_del_object(v___x_4772_);
v___x_4778_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4779_ = l_Lean_MessageData_ofName(v___x_4763_);
lean_inc_ref(v___x_4779_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set_tag(v___x_4776_, 7);
lean_ctor_set(v___x_4776_, 1, v___x_4779_);
lean_ctor_set(v___x_4776_, 0, v___x_4778_);
v___x_4781_ = v___x_4776_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v___x_4779_);
v___x_4781_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4781_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
v___x_4784_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4785_ = l_Lean_indentD(v___x_4784_);
v___x_4786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4783_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
lean_ctor_set(v___x_4789_, 1, v___x_4779_);
v___x_4790_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4789_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v___x_4792_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4791_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4792_;
}
}
else
{
lean_object* v_val_4794_; lean_object* v___x_4796_; 
lean_del_object(v___x_4776_);
lean_dec(v___x_4763_);
lean_dec(v_stx_2365_);
v_val_4794_ = lean_ctor_get(v_fst_4774_, 0);
lean_inc(v_val_4794_);
lean_dec_ref_known(v_fst_4774_, 1);
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v_val_4794_);
v___x_4796_ = v___x_4772_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_val_4794_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v___x_4763_);
lean_dec(v_stx_2365_);
v_a_4801_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4769_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4769_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4809_ = l_Lean_Syntax_getArg(v___x_4761_, v___x_4661_);
lean_dec(v___x_4761_);
v___x_4810_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4811_ = l_Lean_Syntax_isOfKind(v___x_4809_, v___x_4810_);
if (v___x_4811_ == 0)
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v_env_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4812_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4813_ = lean_st_ref_get(v_a_2371_);
v_env_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc_ref(v_env_4814_);
lean_dec(v___x_4813_);
v___x_4815_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4816_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4815_, v_env_4814_, v___x_4812_);
v___x_4817_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4818_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4816_, v___x_4817_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4816_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4849_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4821_ = v___x_4818_;
v_isShared_4822_ = v_isSharedCheck_4849_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4849_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_fst_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4847_; 
v_fst_4823_ = lean_ctor_get(v_a_4819_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_a_4819_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v_a_4819_, 1);
lean_dec(v_unused_4848_);
v___x_4825_ = v_a_4819_;
v_isShared_4826_ = v_isSharedCheck_4847_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_fst_4823_);
lean_dec(v_a_4819_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4847_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
if (lean_obj_tag(v_fst_4823_) == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_del_object(v___x_4821_);
v___x_4827_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4828_ = l_Lean_MessageData_ofName(v___x_4812_);
lean_inc_ref(v___x_4828_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set_tag(v___x_4825_, 7);
lean_ctor_set(v___x_4825_, 1, v___x_4828_);
lean_ctor_set(v___x_4825_, 0, v___x_4827_);
v___x_4830_ = v___x_4825_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4834_ = l_Lean_indentD(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4832_);
lean_ctor_set(v___x_4835_, 1, v___x_4834_);
v___x_4836_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4835_);
lean_ctor_set(v___x_4837_, 1, v___x_4836_);
v___x_4838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
lean_ctor_set(v___x_4838_, 1, v___x_4828_);
v___x_4839_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4840_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4841_;
}
}
else
{
lean_object* v_val_4843_; lean_object* v___x_4845_; 
lean_del_object(v___x_4825_);
lean_dec(v___x_4812_);
lean_dec(v_stx_2365_);
v_val_4843_ = lean_ctor_get(v_fst_4823_, 0);
lean_inc(v_val_4843_);
lean_dec_ref_known(v_fst_4823_, 1);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v_val_4843_);
v___x_4845_ = v___x_4821_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_val_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec(v___x_4812_);
lean_dec(v_stx_2365_);
v_a_4850_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4818_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4818_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_dec(v_stx_2365_);
v___x_4858_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
return v___x_4859_;
}
}
}
}
}
}
else
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4860_ = lean_unsigned_to_nat(1u);
v___x_4861_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4860_);
v___x_4862_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4863_ = l_Lean_Syntax_isOfKind(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v_env_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4864_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4865_ = lean_st_ref_get(v_a_2371_);
v_env_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc_ref(v_env_4866_);
lean_dec(v___x_4865_);
v___x_4867_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4868_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4867_, v_env_4866_, v___x_4864_);
v___x_4869_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4870_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4868_, v___x_4869_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
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
v___x_4879_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
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
v___x_4883_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4886_ = l_Lean_indentD(v___x_4885_);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4884_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4887_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
lean_ctor_set(v___x_4890_, 1, v___x_4880_);
v___x_4891_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4892_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4893_;
}
}
else
{
lean_object* v_val_4895_; lean_object* v___x_4897_; 
lean_del_object(v___x_4877_);
lean_dec(v___x_4864_);
lean_dec(v_stx_2365_);
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
lean_dec(v_stx_2365_);
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
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4910_ = lean_unsigned_to_nat(2u);
v___x_4911_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4910_);
v___x_4912_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4913_ = l_Lean_Syntax_isOfKind(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v_env_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_inc_n(v_stx_2365_, 2);
v___x_4914_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4915_ = lean_st_ref_get(v_a_2371_);
v_env_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc_ref(v_env_4916_);
lean_dec(v___x_4915_);
v___x_4917_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4918_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4917_, v_env_4916_, v___x_4914_);
v___x_4919_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4920_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4918_, v___x_4919_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
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
v___x_4929_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
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
v___x_4933_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4932_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4936_ = l_Lean_indentD(v___x_4935_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4934_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v___x_4930_);
v___x_4941_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4942_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4943_;
}
}
else
{
lean_object* v_val_4945_; lean_object* v___x_4947_; 
lean_del_object(v___x_4927_);
lean_dec(v___x_4914_);
lean_dec(v_stx_2365_);
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
lean_dec(v_stx_2365_);
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
lean_object* v___x_4960_; lean_object* v___x_4961_; 
lean_dec(v_stx_2365_);
v___x_4960_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
return v___x_4961_;
}
}
}
}
else
{
lean_object* v___x_4962_; lean_object* v___x_4963_; uint8_t v___x_4964_; 
v___x_4962_ = lean_unsigned_to_nat(1u);
v___x_4963_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_4962_);
v___x_4964_ = l_Lean_Syntax_isNone(v___x_4963_);
if (v___x_4964_ == 0)
{
uint8_t v___x_4965_; 
v___x_4965_ = l_Lean_Syntax_matchesNull(v___x_4963_, v___x_4962_);
if (v___x_4965_ == 0)
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v_env_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
lean_del_object(v___x_2405_);
lean_inc_n(v_stx_2365_, 2);
v___x_4966_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_4967_ = lean_st_ref_get(v_a_2371_);
v_env_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_env_4968_);
lean_dec(v___x_4967_);
v___x_4969_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4970_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4969_, v_env_4968_, v___x_4966_);
v___x_4971_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4972_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_4970_, v___x_4971_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_4970_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_5003_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4975_ = v___x_4972_;
v_isShared_4976_ = v_isSharedCheck_5003_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4972_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_5003_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v_fst_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_5001_; 
v_fst_4977_ = lean_ctor_get(v_a_4973_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_a_4973_);
if (v_isSharedCheck_5001_ == 0)
{
lean_object* v_unused_5002_; 
v_unused_5002_ = lean_ctor_get(v_a_4973_, 1);
lean_dec(v_unused_5002_);
v___x_4979_ = v_a_4973_;
v_isShared_4980_ = v_isSharedCheck_5001_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_fst_4977_);
lean_dec(v_a_4973_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_5001_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
if (lean_obj_tag(v_fst_4977_) == 0)
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
lean_del_object(v___x_4975_);
v___x_4981_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4982_ = l_Lean_MessageData_ofName(v___x_4966_);
lean_inc_ref(v___x_4982_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set_tag(v___x_4979_, 7);
lean_ctor_set(v___x_4979_, 1, v___x_4982_);
lean_ctor_set(v___x_4979_, 0, v___x_4981_);
v___x_4984_ = v___x_4979_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4981_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4985_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set(v___x_4986_, 1, v___x_4985_);
v___x_4987_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_4988_ = l_Lean_indentD(v___x_4987_);
v___x_4989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4986_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4989_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
lean_ctor_set(v___x_4992_, 1, v___x_4982_);
v___x_4993_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4994_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_4995_;
}
}
else
{
lean_object* v_val_4997_; lean_object* v___x_4999_; 
lean_del_object(v___x_4979_);
lean_dec(v___x_4966_);
lean_dec(v_stx_2365_);
v_val_4997_ = lean_ctor_get(v_fst_4977_, 0);
lean_inc(v_val_4997_);
lean_dec_ref_known(v_fst_4977_, 1);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v_val_4997_);
v___x_4999_ = v___x_4975_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_val_4997_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec(v___x_4966_);
lean_dec(v_stx_2365_);
v_a_5004_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4972_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4972_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
else
{
v___y_2493_ = v_a_2366_;
v___y_2494_ = v_a_2367_;
v___y_2495_ = v_a_2368_;
v___y_2496_ = v_a_2369_;
v___y_2497_ = v_a_2370_;
v___y_2498_ = v_a_2371_;
goto v___jp_2492_;
}
}
else
{
lean_dec(v___x_4963_);
v___y_2493_ = v_a_2366_;
v___y_2494_ = v_a_2367_;
v___y_2495_ = v_a_2368_;
v___y_2496_ = v_a_2369_;
v___y_2497_ = v_a_2370_;
v___y_2498_ = v_a_2371_;
goto v___jp_2492_;
}
}
}
else
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
lean_del_object(v___x_2405_);
v___x_5012_ = lean_unsigned_to_nat(1u);
v___x_5013_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_5012_);
lean_dec(v_stx_2365_);
v___x_5014_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5013_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_5014_;
}
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_del_object(v___x_2405_);
v___x_5015_ = lean_unsigned_to_nat(0u);
v___x_5016_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_5015_);
lean_dec(v_stx_2365_);
v___x_5017_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5016_);
if (lean_obj_tag(v___x_5017_) == 1)
{
lean_object* v_val_5018_; lean_object* v_snd_5019_; lean_object* v_body_5020_; lean_object* v___x_5021_; 
v_val_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_val_5018_);
lean_dec_ref_known(v___x_5017_, 1);
v_snd_5019_ = lean_ctor_get(v_val_5018_, 1);
lean_inc(v_snd_5019_);
lean_dec(v_val_5018_);
v_body_5020_ = lean_ctor_get(v_snd_5019_, 1);
lean_inc(v_body_5020_);
lean_dec(v_snd_5019_);
v___x_5021_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5020_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5042_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5024_ = v___x_5021_;
v_isShared_5025_ = v_isSharedCheck_5042_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5042_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
uint8_t v_breaks_5026_; uint8_t v_continues_5027_; uint8_t v_returnsEarly_5028_; lean_object* v_reassigns_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5040_; 
v_breaks_5026_ = lean_ctor_get_uint8(v_a_5022_, sizeof(void*)*2);
v_continues_5027_ = lean_ctor_get_uint8(v_a_5022_, sizeof(void*)*2 + 1);
v_returnsEarly_5028_ = lean_ctor_get_uint8(v_a_5022_, sizeof(void*)*2 + 2);
v_reassigns_5029_ = lean_ctor_get(v_a_5022_, 1);
v_isSharedCheck_5040_ = !lean_is_exclusive(v_a_5022_);
if (v_isSharedCheck_5040_ == 0)
{
lean_object* v_unused_5041_; 
v_unused_5041_ = lean_ctor_get(v_a_5022_, 0);
lean_dec(v_unused_5041_);
v___x_5031_ = v_a_5022_;
v_isShared_5032_ = v_isSharedCheck_5040_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_reassigns_5029_);
lean_dec(v_a_5022_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5040_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5033_; lean_object* v___x_5035_; 
v___x_5033_ = lean_unsigned_to_nat(1u);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v___x_5033_);
v___x_5035_ = v___x_5031_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v_reassigns_5029_);
lean_ctor_set_uint8(v_reuseFailAlloc_5039_, sizeof(void*)*2, v_breaks_5026_);
lean_ctor_set_uint8(v_reuseFailAlloc_5039_, sizeof(void*)*2 + 1, v_continues_5027_);
lean_ctor_set_uint8(v_reuseFailAlloc_5039_, sizeof(void*)*2 + 2, v_returnsEarly_5028_);
v___x_5035_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
lean_object* v___x_5037_; 
lean_ctor_set_uint8(v___x_5035_, sizeof(void*)*2 + 3, v___x_2609_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 0, v___x_5035_);
v___x_5037_ = v___x_5024_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5035_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
}
else
{
return v___x_5021_;
}
}
else
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec(v___x_5017_);
v___x_5043_ = lean_unsigned_to_nat(1u);
v___x_5044_ = l_Lean_NameSet_empty;
v___x_5045_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2, v___x_2609_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 1, v___x_2609_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 2, v___x_2609_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 3, v___x_2609_);
v___x_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5045_);
return v___x_5046_;
}
}
}
else
{
lean_object* v___x_5047_; lean_object* v___x_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; 
lean_del_object(v___x_2405_);
v___x_5047_ = lean_unsigned_to_nat(0u);
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_5052_);
v___x_5054_ = l_Lean_Syntax_isNone(v___x_5053_);
if (v___x_5054_ == 0)
{
uint8_t v___x_5055_; 
v___x_5055_ = l_Lean_Syntax_matchesNull(v___x_5053_, v___x_5052_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v_env_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_inc_n(v_stx_2365_, 2);
v___x_5056_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_5057_ = lean_st_ref_get(v_a_2371_);
v_env_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc_ref(v_env_5058_);
lean_dec(v___x_5057_);
v___x_5059_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5060_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5059_, v_env_5058_, v___x_5056_);
v___x_5061_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5062_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_5060_, v___x_5061_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_5060_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5093_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5065_ = v___x_5062_;
v_isShared_5066_ = v_isSharedCheck_5093_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5093_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v_fst_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5091_; 
v_fst_5067_ = lean_ctor_get(v_a_5063_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v_a_5063_);
if (v_isSharedCheck_5091_ == 0)
{
lean_object* v_unused_5092_; 
v_unused_5092_ = lean_ctor_get(v_a_5063_, 1);
lean_dec(v_unused_5092_);
v___x_5069_ = v_a_5063_;
v_isShared_5070_ = v_isSharedCheck_5091_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_fst_5067_);
lean_dec(v_a_5063_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5091_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
if (lean_obj_tag(v_fst_5067_) == 0)
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5074_; 
lean_del_object(v___x_5065_);
v___x_5071_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_5072_ = l_Lean_MessageData_ofName(v___x_5056_);
lean_inc_ref(v___x_5072_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set_tag(v___x_5069_, 7);
lean_ctor_set(v___x_5069_, 1, v___x_5072_);
lean_ctor_set(v___x_5069_, 0, v___x_5071_);
v___x_5074_ = v___x_5069_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5075_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_5078_ = l_Lean_indentD(v___x_5077_);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5076_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5081_);
lean_ctor_set(v___x_5082_, 1, v___x_5072_);
v___x_5083_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_5084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5082_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
v___x_5085_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5084_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_5085_;
}
}
else
{
lean_object* v_val_5087_; lean_object* v___x_5089_; 
lean_del_object(v___x_5069_);
lean_dec(v___x_5056_);
lean_dec(v_stx_2365_);
v_val_5087_ = lean_ctor_get(v_fst_5067_, 0);
lean_inc(v_val_5087_);
lean_dec_ref_known(v_fst_5067_, 1);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v_val_5087_);
v___x_5089_ = v___x_5065_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_val_5087_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v___x_5056_);
lean_dec(v_stx_2365_);
v_a_5094_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5062_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5062_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
else
{
lean_dec(v_stx_2365_);
goto v___jp_5048_;
}
}
else
{
lean_dec(v___x_5053_);
lean_dec(v_stx_2365_);
goto v___jp_5048_;
}
v___jp_5048_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5049_ = l_Lean_NameSet_empty;
v___x_5050_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5050_, 0, v___x_5047_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*2, v___x_2607_);
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*2 + 1, v___x_2607_);
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*2 + 2, v___x_2605_);
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*2 + 3, v___x_2605_);
v___x_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
return v___x_5051_;
}
}
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
lean_del_object(v___x_2405_);
lean_dec(v_stx_2365_);
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = l_Lean_NameSet_empty;
v___x_5104_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5104_, 0, v___x_5102_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
lean_ctor_set_uint8(v___x_5104_, sizeof(void*)*2, v___x_2604_);
lean_ctor_set_uint8(v___x_5104_, sizeof(void*)*2 + 1, v___x_2605_);
lean_ctor_set_uint8(v___x_5104_, sizeof(void*)*2 + 2, v___x_2604_);
lean_ctor_set_uint8(v___x_5104_, sizeof(void*)*2 + 3, v___x_2605_);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
else
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_del_object(v___x_2405_);
lean_dec(v_stx_2365_);
v___x_5106_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
return v___x_5107_;
}
v___jp_2421_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2428_ = lean_unsigned_to_nat(2u);
v___x_2429_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2431_ = l_Lean_Syntax_isOfKind(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_env_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_inc_n(v_stx_2365_, 2);
v___x_2432_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2433_ = lean_st_ref_get(v___y_2427_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_ref(v_env_2434_);
lean_dec(v___x_2433_);
v___x_2435_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2436_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2435_, v_env_2434_, v___x_2432_);
v___x_2437_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2438_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2436_, v___x_2437_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___x_2436_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2469_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2469_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2469_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_fst_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2467_; 
v_fst_2443_ = lean_ctor_get(v_a_2439_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_a_2439_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v_a_2439_, 1);
lean_dec(v_unused_2468_);
v___x_2445_ = v_a_2439_;
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_fst_2443_);
lean_dec(v_a_2439_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
if (lean_obj_tag(v_fst_2443_) == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
lean_del_object(v___x_2441_);
v___x_2447_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2448_ = l_Lean_MessageData_ofName(v___x_2432_);
lean_inc_ref(v___x_2448_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 7);
lean_ctor_set(v___x_2445_, 1, v___x_2448_);
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2450_ = v___x_2445_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2451_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2454_ = l_Lean_indentD(v___x_2453_);
v___x_2455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2452_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___x_2448_);
v___x_2459_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2460_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
return v___x_2461_;
}
}
else
{
lean_object* v_val_2463_; lean_object* v___x_2465_; 
lean_del_object(v___x_2445_);
lean_dec(v___x_2432_);
lean_dec(v_stx_2365_);
v_val_2463_ = lean_ctor_get(v_fst_2443_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v_fst_2443_, 1);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v_val_2463_);
v___x_2465_ = v___x_2441_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_val_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v___x_2432_);
lean_dec(v_stx_2365_);
v_a_2470_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2438_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2438_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2478_ = lean_unsigned_to_nat(7u);
v___x_2479_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2478_);
v___x_2480_ = lean_unsigned_to_nat(8u);
v___x_2481_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2480_);
lean_dec(v_stx_2365_);
v___x_2482_ = l_Lean_Syntax_getOptional_x3f(v___x_2481_);
lean_dec(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_box(0);
v___y_2379_ = v___y_2425_;
v___y_2380_ = v___y_2423_;
v___y_2381_ = v___x_2479_;
v___y_2382_ = v___y_2426_;
v___y_2383_ = v___y_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___x_2483_;
goto v___jp_2378_;
}
else
{
lean_object* v_val_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_val_2484_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_val_2484_);
lean_dec(v___x_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_val_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v___y_2379_ = v___y_2425_;
v___y_2380_ = v___y_2423_;
v___y_2381_ = v___x_2479_;
v___y_2382_ = v___y_2426_;
v___y_2383_ = v___y_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___x_2489_;
goto v___jp_2378_;
}
}
}
}
}
v___jp_2492_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2499_ = lean_unsigned_to_nat(2u);
v___x_2500_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2499_);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2502_ = l_Lean_Syntax_isOfKind(v___x_2500_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_env_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_del_object(v___x_2405_);
lean_inc_n(v_stx_2365_, 2);
v___x_2503_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2504_ = lean_st_ref_get(v___y_2498_);
v_env_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc_ref(v_env_2505_);
lean_dec(v___x_2504_);
v___x_2506_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2507_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2506_, v_env_2505_, v___x_2503_);
v___x_2508_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2509_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2507_, v___x_2508_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___x_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2540_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2540_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2540_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_fst_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2538_; 
v_fst_2514_ = lean_ctor_get(v_a_2510_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2510_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_a_2510_, 1);
lean_dec(v_unused_2539_);
v___x_2516_ = v_a_2510_;
v_isShared_2517_ = v_isSharedCheck_2538_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_fst_2514_);
lean_dec(v_a_2510_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2538_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
if (lean_obj_tag(v_fst_2514_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_del_object(v___x_2512_);
v___x_2518_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2519_ = l_Lean_MessageData_ofName(v___x_2503_);
lean_inc_ref(v___x_2519_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 7);
lean_ctor_set(v___x_2516_, 1, v___x_2519_);
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2521_ = v___x_2516_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2525_ = l_Lean_indentD(v___x_2524_);
v___x_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2523_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___x_2519_);
v___x_2530_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2531_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2532_;
}
}
else
{
lean_object* v_val_2534_; lean_object* v___x_2536_; 
lean_del_object(v___x_2516_);
lean_dec(v___x_2503_);
lean_dec(v_stx_2365_);
v_val_2534_ = lean_ctor_get(v_fst_2514_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v_fst_2514_, 1);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v_val_2534_);
v___x_2536_ = v___x_2512_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_val_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v___x_2503_);
lean_dec(v_stx_2365_);
v_a_2541_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2509_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2509_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2549_ = lean_unsigned_to_nat(3u);
v___x_2550_ = l_Lean_Syntax_getArg(v_stx_2365_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2552_ = l_Lean_Syntax_isOfKind(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_env_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_del_object(v___x_2405_);
lean_inc_n(v_stx_2365_, 2);
v___x_2553_ = l_Lean_Syntax_getKind(v_stx_2365_);
v___x_2554_ = lean_st_ref_get(v___y_2498_);
v_env_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_ref(v_env_2555_);
lean_dec(v___x_2554_);
v___x_2556_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2557_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2556_, v_env_2555_, v___x_2553_);
v___x_2558_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2559_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2365_, v___x_2557_, v___x_2558_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___x_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2590_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_fst_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2588_; 
v_fst_2564_ = lean_ctor_get(v_a_2560_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_a_2560_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_a_2560_, 1);
lean_dec(v_unused_2589_);
v___x_2566_ = v_a_2560_;
v_isShared_2567_ = v_isSharedCheck_2588_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_fst_2564_);
lean_dec(v_a_2560_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2588_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
if (lean_obj_tag(v_fst_2564_) == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_del_object(v___x_2562_);
v___x_2568_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2569_ = l_Lean_MessageData_ofName(v___x_2553_);
lean_inc_ref(v___x_2569_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 7);
lean_ctor_set(v___x_2566_, 1, v___x_2569_);
lean_ctor_set(v___x_2566_, 0, v___x_2568_);
v___x_2571_ = v___x_2566_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2572_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_MessageData_ofSyntax(v_stx_2365_);
v___x_2575_ = l_Lean_indentD(v___x_2574_);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2573_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___x_2569_);
v___x_2580_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2581_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2582_;
}
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2586_; 
lean_del_object(v___x_2566_);
lean_dec(v___x_2553_);
lean_dec(v_stx_2365_);
v_val_2584_ = lean_ctor_get(v_fst_2564_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v_fst_2564_, 1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_val_2584_);
v___x_2586_ = v___x_2562_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_val_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v___x_2553_);
lean_dec(v_stx_2365_);
v_a_2591_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2559_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2559_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_stx_2365_);
v___x_2599_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2599_);
v___x_2601_ = v___x_2405_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
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
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_stx_2365_);
v_a_5109_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_2402_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_2402_);
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
v___jp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2374_, v_bodyInfo_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
v___jp_2378_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2387_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2381_);
v___x_2390_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2387_, v___x_2388_, v___x_2389_, v___y_2386_, v___y_2384_, v___y_2380_, v___y_2385_, v___y_2379_, v___y_2382_, v___y_2383_);
return v___x_2390_;
}
v___jp_2391_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
v___jp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2395_, v_bodyInfo_2396_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5117_, size_t v_sz_5118_, size_t v_i_5119_, lean_object* v_b_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
uint8_t v___x_5128_; 
v___x_5128_ = lean_usize_dec_lt(v_i_5119_, v_sz_5118_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v_b_5120_);
return v___x_5129_;
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5131_; 
v_a_5130_ = lean_array_uget_borrowed(v_as_5117_, v_i_5119_);
lean_inc(v_a_5130_);
v___x_5131_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5130_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5133_; size_t v___x_5134_; size_t v___x_5135_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5131_, 1);
v___x_5133_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5120_, v_a_5132_);
v___x_5134_ = ((size_t)1ULL);
v___x_5135_ = lean_usize_add(v_i_5119_, v___x_5134_);
v_i_5119_ = v___x_5135_;
v_b_5120_ = v___x_5133_;
goto _start;
}
else
{
lean_dec_ref(v_b_5120_);
return v___x_5131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_info_5145_; lean_object* v___x_5146_; size_t v_sz_5147_; size_t v___x_5148_; lean_object* v___x_5149_; 
v_info_5145_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5146_ = l_Lean_Parser_Term_getDoElems(v_stx_5137_);
v_sz_5147_ = lean_array_size(v___x_5146_);
v___x_5148_ = ((size_t)0ULL);
v___x_5149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5146_, v_sz_5147_, v___x_5148_, v_info_5145_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_);
lean_dec_ref(v___x_5146_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec(v_a_5161_);
lean_dec_ref(v_a_5160_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5168_, lean_object* v_sz_5169_, lean_object* v_i_5170_, lean_object* v_b_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
size_t v_sz_boxed_5179_; size_t v_i_boxed_5180_; lean_object* v_res_5181_; 
v_sz_boxed_5179_ = lean_unbox_usize(v_sz_5169_);
lean_dec(v_sz_5169_);
v_i_boxed_5180_ = lean_unbox_usize(v_i_5170_);
lean_dec(v_i_5170_);
v_res_5181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5168_, v_sz_boxed_5179_, v_i_boxed_5180_, v_b_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec_ref(v_as_5168_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5182_, lean_object* v_sz_5183_, lean_object* v_i_5184_, lean_object* v_b_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
size_t v_sz_boxed_5193_; size_t v_i_boxed_5194_; lean_object* v_res_5195_; 
v_sz_boxed_5193_ = lean_unbox_usize(v_sz_5183_);
lean_dec(v_sz_5183_);
v_i_boxed_5194_ = lean_unbox_usize(v_i_5184_);
lean_dec(v_i_5184_);
v_res_5195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5182_, v_sz_boxed_5193_, v_i_boxed_5194_, v_b_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec_ref(v_as_5182_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5196_, lean_object* v_rhs_x3f_5197_, lean_object* v_otherwise_x3f_5198_, lean_object* v_body_x3f_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5196_, v_rhs_x3f_5197_, v_otherwise_x3f_5198_, v_body_x3f_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_);
lean_dec(v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec(v_a_5203_);
lean_dec_ref(v_a_5202_);
lean_dec(v_a_5201_);
lean_dec_ref(v_a_5200_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5208_, lean_object* v_as_5209_, lean_object* v_sz_5210_, lean_object* v_i_5211_, lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
uint8_t v___x_176220__boxed_5220_; size_t v_sz_boxed_5221_; size_t v_i_boxed_5222_; lean_object* v_res_5223_; 
v___x_176220__boxed_5220_ = lean_unbox(v___x_5208_);
v_sz_boxed_5221_ = lean_unbox_usize(v_sz_5210_);
lean_dec(v_sz_5210_);
v_i_boxed_5222_ = lean_unbox_usize(v_i_5211_);
lean_dec(v_i_5211_);
v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_176220__boxed_5220_, v_as_5209_, v_sz_boxed_5221_, v_i_boxed_5222_, v_b_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec_ref(v_as_5209_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5224_, lean_object* v_as_5225_, lean_object* v_sz_5226_, lean_object* v_i_5227_, lean_object* v_b_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
uint8_t v___x_176267__boxed_5236_; size_t v_sz_boxed_5237_; size_t v_i_boxed_5238_; lean_object* v_res_5239_; 
v___x_176267__boxed_5236_ = lean_unbox(v___x_5224_);
v_sz_boxed_5237_ = lean_unbox_usize(v_sz_5226_);
lean_dec(v_sz_5226_);
v_i_boxed_5238_ = lean_unbox_usize(v_i_5227_);
lean_dec(v_i_5227_);
v_res_5239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_176267__boxed_5236_, v_as_5225_, v_sz_boxed_5237_, v_i_boxed_5238_, v_b_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec_ref(v_as_5225_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5240_, lean_object* v_sz_5241_, lean_object* v_i_5242_, lean_object* v_b_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
size_t v_sz_boxed_5251_; size_t v_i_boxed_5252_; lean_object* v_res_5253_; 
v_sz_boxed_5251_ = lean_unbox_usize(v_sz_5241_);
lean_dec(v_sz_5241_);
v_i_boxed_5252_ = lean_unbox_usize(v_i_5242_);
lean_dec(v_i_5242_);
v_res_5253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5240_, v_sz_boxed_5251_, v_i_boxed_5252_, v_b_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec_ref(v_as_5240_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5254_, lean_object* v_decl_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
uint8_t v_reassignment_boxed_5263_; lean_object* v_res_5264_; 
v_reassignment_boxed_5263_ = lean_unbox(v_reassignment_5254_);
v_res_5264_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5263_, v_decl_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5292_, lean_object* v_ref_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5293_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5302_, lean_object* v_ref_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5302_, v_ref_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5312_, lean_object* v_x_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5322_, lean_object* v_x_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5322_, v_x_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec(v___y_5325_);
lean_dec_ref(v___y_5324_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5332_, lean_object* v_as_5333_, lean_object* v_as_x27_5334_, lean_object* v_b_5335_, lean_object* v_a_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v___x_5344_; 
v___x_5344_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5332_, v_as_x27_5334_, v_b_5335_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
return v___x_5344_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5345_, lean_object* v_as_5346_, lean_object* v_as_x27_5347_, lean_object* v_b_5348_, lean_object* v_a_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5345_, v_as_5346_, v_as_x27_5347_, v_b_5348_, v_a_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v_as_x27_5347_);
lean_dec(v_as_5346_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5358_, lean_object* v_msg_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_msg_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5368_, v_msg_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5378_, lean_object* v_msg_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
lean_object* v___x_5387_; 
v___x_5387_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5378_, v_msg_5379_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5388_, lean_object* v_msg_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5388_, v_msg_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5398_, lean_object* v_as_x27_5399_, lean_object* v_b_5400_, lean_object* v_a_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5399_, v_b_5400_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5410_, lean_object* v_as_x27_5411_, lean_object* v_b_5412_, lean_object* v_a_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5410_, v_as_x27_5411_, v_b_5412_, v_a_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v_as_x27_5411_);
lean_dec(v_as_5410_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5422_, lean_object* v_ref_5423_, lean_object* v_msg_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v___x_5432_; 
v___x_5432_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5423_, v_msg_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5433_, lean_object* v_ref_5434_, lean_object* v_msg_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5433_, v_ref_5434_, v_msg_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
lean_dec(v_ref_5434_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5444_, lean_object* v_macroStack_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5444_, v_macroStack_5445_, v___y_5450_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5454_, lean_object* v_macroStack_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5454_, v_macroStack_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5464_, lean_object* v_m_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v___x_5467_; 
v___x_5467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5465_, v_a_5466_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5468_, lean_object* v_m_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v_res_5471_; 
v_res_5471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5468_, v_m_5469_, v_a_5470_);
lean_dec(v_a_5470_);
lean_dec_ref(v_m_5469_);
return v_res_5471_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5472_, lean_object* v_x_5473_, lean_object* v_x_5474_){
_start:
{
uint8_t v___x_5475_; 
v___x_5475_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5473_, v_x_5474_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5476_, lean_object* v_x_5477_, lean_object* v_x_5478_){
_start:
{
uint8_t v_res_5479_; lean_object* v_r_5480_; 
v_res_5479_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5476_, v_x_5477_, v_x_5478_);
lean_dec_ref(v_x_5478_);
lean_dec_ref(v_x_5477_);
v_r_5480_ = lean_box(v_res_5479_);
return v_r_5480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5481_, lean_object* v_a_5482_, lean_object* v_x_5483_){
_start:
{
lean_object* v___x_5484_; 
v___x_5484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5482_, v_x_5483_);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5485_, lean_object* v_a_5486_, lean_object* v_x_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5485_, v_a_5486_, v_x_5487_);
lean_dec(v_x_5487_);
lean_dec(v_a_5486_);
return v_res_5488_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5489_, lean_object* v_x_5490_, size_t v_x_5491_, lean_object* v_x_5492_){
_start:
{
uint8_t v___x_5493_; 
v___x_5493_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5490_, v_x_5491_, v_x_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5494_, lean_object* v_x_5495_, lean_object* v_x_5496_, lean_object* v_x_5497_){
_start:
{
size_t v_x_183282__boxed_5498_; uint8_t v_res_5499_; lean_object* v_r_5500_; 
v_x_183282__boxed_5498_ = lean_unbox_usize(v_x_5496_);
lean_dec(v_x_5496_);
v_res_5499_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5494_, v_x_5495_, v_x_183282__boxed_5498_, v_x_5497_);
lean_dec_ref(v_x_5497_);
lean_dec_ref(v_x_5495_);
v_r_5500_ = lean_box(v_res_5499_);
return v_r_5500_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5501_, lean_object* v_keys_5502_, lean_object* v_vals_5503_, lean_object* v_heq_5504_, lean_object* v_i_5505_, lean_object* v_k_5506_){
_start:
{
uint8_t v___x_5507_; 
v___x_5507_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5502_, v_i_5505_, v_k_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5508_, lean_object* v_keys_5509_, lean_object* v_vals_5510_, lean_object* v_heq_5511_, lean_object* v_i_5512_, lean_object* v_k_5513_){
_start:
{
uint8_t v_res_5514_; lean_object* v_r_5515_; 
v_res_5514_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5508_, v_keys_5509_, v_vals_5510_, v_heq_5511_, v_i_5512_, v_k_5513_);
lean_dec_ref(v_k_5513_);
lean_dec_ref(v_vals_5510_);
lean_dec_ref(v_keys_5509_);
v_r_5515_ = lean_box(v_res_5514_);
return v_r_5515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v___x_5524_; 
v___x_5524_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_a_5531_);
lean_dec_ref(v_a_5530_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
lean_dec(v_a_5527_);
lean_dec_ref(v_a_5526_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_){
_start:
{
lean_object* v___x_5542_; 
v___x_5542_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_);
return v___x_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_){
_start:
{
lean_object* v_res_5551_; 
v_res_5551_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_);
lean_dec(v_a_5549_);
lean_dec_ref(v_a_5548_);
lean_dec(v_a_5547_);
lean_dec_ref(v_a_5546_);
lean_dec(v_a_5545_);
lean_dec_ref(v_a_5544_);
return v_res_5551_;
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
