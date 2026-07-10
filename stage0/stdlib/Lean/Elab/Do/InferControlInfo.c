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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 236, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value;
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
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83;
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_25_; uint8_t v___y_26_; lean_object* v___y_27_; uint8_t v___y_28_; uint8_t v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_27_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_25_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_28_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_26_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_29_);
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
v___y_25_ = v_numRegularExits_39_;
v___y_26_ = v___y_36_;
v___y_27_ = v_reassigns_41_;
v___y_28_ = v___y_37_;
v___y_29_ = v___y_38_;
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
v___y_25_ = v_numRegularExits_42_;
v___y_26_ = v___y_36_;
v___y_27_ = v_reassigns_43_;
v___y_28_ = v___y_37_;
v___y_29_ = v___y_38_;
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
uint8_t v___y_57_; uint8_t v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; uint8_t v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_59_, v___y_60_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_62_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_58_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_61_);
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
v___y_58_ = v___y_73_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v_reassigns_78_;
v___y_61_ = v___y_74_;
v___y_62_ = v___x_79_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_75_;
v___y_58_ = v___y_73_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v_reassigns_78_;
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
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(1);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_336_; 
v_head_313_ = lean_ctor_get(v_x_312_, 0);
v_tail_314_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_336_ == 0)
{
v___x_316_ = v_x_312_;
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_tail_314_);
lean_inc(v_head_313_);
lean_dec(v_x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_before_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_334_; 
v_before_318_ = lean_ctor_get(v_head_313_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_head_313_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_head_313_, 1);
lean_dec(v_unused_335_);
v___x_320_ = v_head_313_;
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_before_318_);
lean_dec(v_head_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 7);
lean_ctor_set(v___x_320_, 1, v___x_322_);
lean_ctor_set(v___x_320_, 0, v_x_311_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_x_311_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_333_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 7);
lean_ctor_set(v___x_316_, 1, v___x_325_);
lean_ctor_set(v___x_316_, 0, v___x_324_);
v___x_327_ = v___x_316_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_332_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_MessageData_ofSyntax(v_before_318_);
v___x_329_ = l_Lean_indentD(v___x_328_);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v_x_311_ = v___x_330_;
v_x_312_ = v_tail_314_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_337_, lean_object* v_opt_338_){
_start:
{
lean_object* v_name_339_; lean_object* v_defValue_340_; lean_object* v_map_341_; lean_object* v___x_342_; 
v_name_339_ = lean_ctor_get(v_opt_338_, 0);
v_defValue_340_ = lean_ctor_get(v_opt_338_, 1);
v_map_341_ = lean_ctor_get(v_opts_337_, 0);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_341_, v_name_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_unbox(v_defValue_340_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_val_344_) == 1)
{
uint8_t v_v_345_; 
v_v_345_ = lean_ctor_get_uint8(v_val_344_, 0);
lean_dec_ref_known(v_val_344_, 0);
return v_v_345_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_val_344_);
v___x_346_ = lean_unbox(v_defValue_340_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_355_ = l_Lean_MessageData_ofFormat(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_356_, lean_object* v_macroStack_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_options_360_; lean_object* v___x_361_; uint8_t v___x_362_; uint8_t v___x_363_; 
v_options_360_ = lean_ctor_get(v___y_358_, 2);
v___x_361_ = l_Lean_Elab_pp_macroStack;
v___x_362_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_360_, v___x_361_);
v___x_363_ = lean_bool_not(v___x_362_);
if (v___x_363_ == 0)
{
if (lean_obj_tag(v_macroStack_357_) == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_msgData_356_);
return v___x_364_;
}
else
{
lean_object* v_head_365_; lean_object* v_after_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_381_; 
v_head_365_ = lean_ctor_get(v_macroStack_357_, 0);
lean_inc(v_head_365_);
v_after_366_ = lean_ctor_get(v_head_365_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_head_365_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_head_365_, 0);
lean_dec(v_unused_382_);
v___x_368_ = v_head_365_;
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_after_366_);
lean_dec(v_head_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 7);
lean_ctor_set(v___x_368_, 1, v___x_370_);
lean_ctor_set(v___x_368_, 0, v_msgData_356_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_msgData_356_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_380_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_msgData_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_373_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_MessageData_ofSyntax(v_after_366_);
v___x_376_ = l_Lean_indentD(v___x_375_);
v_msgData_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_377_, 0, v___x_374_);
lean_ctor_set(v_msgData_377_, 1, v___x_376_);
v___x_378_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_377_, v_macroStack_357_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec(v_macroStack_357_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_msgData_356_);
return v___x_383_;
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
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v_a_399_; lean_object* v_macroStack_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_ref_397_ = lean_ctor_get(v___y_394_, 5);
v___x_398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_389_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
v_macroStack_400_ = lean_ctor_get(v___y_390_, 1);
v___x_401_ = l_Lean_Elab_getBetterRef(v_ref_397_, v_macroStack_400_);
lean_inc(v_macroStack_400_);
v___x_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_399_, v_macroStack_400_, v___y_394_);
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
lean_ctor_set(v___x_407_, 0, v___x_401_);
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_464_, size_t v_i_465_, lean_object* v_bs_466_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_bs_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_480_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_479_, v_i_boxed_480_, v_bs_478_);
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
uint8_t v___x_281463__boxed_524_; uint8_t v___x_281464__boxed_525_; size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v___x_281463__boxed_524_ = lean_unbox(v___x_518_);
v___x_281464__boxed_525_ = lean_unbox(v___x_519_);
v_i_boxed_526_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_281463__boxed_524_, v___x_281464__boxed_525_, v_as_520_, v_i_boxed_526_, v_stop_boxed_527_, v_b_523_);
lean_dec_ref(v_as_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_529_, lean_object* v_declName_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v___x_533_; lean_object* v_env_534_; lean_object* v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; 
v___x_533_ = 0;
v_env_534_ = l_Lean_Environment_setExporting(v_env_529_, v___x_533_);
lean_inc(v_declName_530_);
v___x_535_ = l_Lean_mkPrivateName(v_env_534_, v_declName_530_);
v___x_536_ = 1;
lean_inc_ref(v_env_534_);
v___x_537_ = l_Lean_Environment_contains(v_env_534_, v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = l_Lean_privateToUserName(v_declName_530_);
v___x_539_ = l_Lean_Environment_contains(v_env_534_, v___x_538_, v___x_536_);
v___x_540_ = lean_box(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___y_532_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec_ref(v_env_534_);
lean_dec(v_declName_530_);
v___x_542_ = lean_box(v___x_537_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___y_532_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_544_, lean_object* v_declName_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_544_, v_declName_545_, v___y_546_, v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_548_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = l_Lean_maxRecDepthErrorMessage;
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_557_ = l_Lean_MessageData_ofFormat(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_559_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_560_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_561_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_ref_561_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_569_, lean_object* v___y_570_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_571_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_571_);
lean_ctor_set(v___x_572_, 1, v___y_570_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_573_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_573_);
lean_ctor_set(v___x_574_, 1, v___y_570_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_575_, v___y_576_);
lean_dec_ref(v_x_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_578_, lean_object* v_stx_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_578_, v_stx_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
if (lean_obj_tag(v_a_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_a_584_ = lean_ctor_get(v___x_582_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_593_);
v___x_586_ = v___x_582_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_a_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_622_; 
v_val_594_ = lean_ctor_get(v_a_583_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_a_583_);
if (v_isSharedCheck_622_ == 0)
{
v___x_596_ = v_a_583_;
v_isShared_597_ = v_isSharedCheck_622_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v_a_583_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_622_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_snd_598_; 
v_snd_598_ = lean_ctor_get(v_val_594_, 1);
lean_inc(v_snd_598_);
lean_dec(v_val_594_);
if (lean_obj_tag(v_snd_598_) == 0)
{
lean_object* v_a_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
lean_del_object(v___x_596_);
v_a_599_ = lean_ctor_get(v___x_582_, 1);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_582_, 2);
v_a_600_ = lean_ctor_get(v_snd_598_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v_snd_598_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v_snd_598_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v_snd_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_605_, v_a_599_);
lean_dec_ref(v___x_605_);
return v___x_606_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_a_609_ = lean_ctor_get(v___x_582_, 1);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_582_, 2);
v_a_610_ = lean_ctor_get(v_snd_598_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_snd_598_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v_snd_598_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v_snd_598_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_a_610_);
v___x_615_ = v___x_596_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_620_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_615_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_617_, v_a_609_);
lean_dec_ref(v___x_617_);
return v___x_618_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_a_623_ = lean_ctor_get(v___x_582_, 0);
v_a_624_ = lean_ctor_get(v___x_582_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_582_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_dec(v___x_582_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_632_, lean_object* v_stx_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_632_, v_stx_633_, v___y_634_, v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_637_, lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_fileName_646_; lean_object* v_fileMap_647_; lean_object* v_options_648_; lean_object* v_currRecDepth_649_; lean_object* v_maxRecDepth_650_; lean_object* v_ref_651_; lean_object* v_currNamespace_652_; lean_object* v_openDecls_653_; lean_object* v_initHeartbeats_654_; lean_object* v_maxHeartbeats_655_; lean_object* v_quotContext_656_; lean_object* v_currMacroScope_657_; uint8_t v_diag_658_; lean_object* v_cancelTk_x3f_659_; uint8_t v_suppressElabErrors_660_; lean_object* v_inheritedTraceOptions_661_; lean_object* v_ref_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_fileName_646_ = lean_ctor_get(v___y_643_, 0);
v_fileMap_647_ = lean_ctor_get(v___y_643_, 1);
v_options_648_ = lean_ctor_get(v___y_643_, 2);
v_currRecDepth_649_ = lean_ctor_get(v___y_643_, 3);
v_maxRecDepth_650_ = lean_ctor_get(v___y_643_, 4);
v_ref_651_ = lean_ctor_get(v___y_643_, 5);
v_currNamespace_652_ = lean_ctor_get(v___y_643_, 6);
v_openDecls_653_ = lean_ctor_get(v___y_643_, 7);
v_initHeartbeats_654_ = lean_ctor_get(v___y_643_, 8);
v_maxHeartbeats_655_ = lean_ctor_get(v___y_643_, 9);
v_quotContext_656_ = lean_ctor_get(v___y_643_, 10);
v_currMacroScope_657_ = lean_ctor_get(v___y_643_, 11);
v_diag_658_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*14);
v_cancelTk_x3f_659_ = lean_ctor_get(v___y_643_, 12);
v_suppressElabErrors_660_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_661_ = lean_ctor_get(v___y_643_, 13);
v_ref_662_ = l_Lean_replaceRef(v_ref_637_, v_ref_651_);
lean_inc_ref(v_inheritedTraceOptions_661_);
lean_inc(v_cancelTk_x3f_659_);
lean_inc(v_currMacroScope_657_);
lean_inc(v_quotContext_656_);
lean_inc(v_maxHeartbeats_655_);
lean_inc(v_initHeartbeats_654_);
lean_inc(v_openDecls_653_);
lean_inc(v_currNamespace_652_);
lean_inc(v_maxRecDepth_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_options_648_);
lean_inc_ref(v_fileMap_647_);
lean_inc_ref(v_fileName_646_);
v___x_663_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_663_, 0, v_fileName_646_);
lean_ctor_set(v___x_663_, 1, v_fileMap_647_);
lean_ctor_set(v___x_663_, 2, v_options_648_);
lean_ctor_set(v___x_663_, 3, v_currRecDepth_649_);
lean_ctor_set(v___x_663_, 4, v_maxRecDepth_650_);
lean_ctor_set(v___x_663_, 5, v_ref_662_);
lean_ctor_set(v___x_663_, 6, v_currNamespace_652_);
lean_ctor_set(v___x_663_, 7, v_openDecls_653_);
lean_ctor_set(v___x_663_, 8, v_initHeartbeats_654_);
lean_ctor_set(v___x_663_, 9, v_maxHeartbeats_655_);
lean_ctor_set(v___x_663_, 10, v_quotContext_656_);
lean_ctor_set(v___x_663_, 11, v_currMacroScope_657_);
lean_ctor_set(v___x_663_, 12, v_cancelTk_x3f_659_);
lean_ctor_set(v___x_663_, 13, v_inheritedTraceOptions_661_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*14, v_diag_658_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*14 + 1, v_suppressElabErrors_660_);
v___x_664_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___x_663_, v___y_644_);
lean_dec_ref_known(v___x_663_, 14);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v_ref_665_);
return v_res_674_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; double v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_float_of_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_680_, lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_733_; 
v_ref_687_ = lean_ctor_get(v___y_684_, 5);
v___x_688_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_733_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_733_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_733_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_traceState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_cache_699_; lean_object* v_messages_700_; lean_object* v_infoState_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_732_; 
v___x_693_ = lean_st_ref_take(v___y_685_);
v_traceState_694_ = lean_ctor_get(v___x_693_, 4);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_cache_699_ = lean_ctor_get(v___x_693_, 5);
v_messages_700_ = lean_ctor_get(v___x_693_, 6);
v_infoState_701_ = lean_ctor_get(v___x_693_, 7);
v_snapshotTasks_702_ = lean_ctor_get(v___x_693_, 8);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_732_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_732_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_701_);
lean_inc(v_messages_700_);
lean_inc(v_cache_699_);
lean_inc(v_traceState_694_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_732_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint64_t v_tid_706_; lean_object* v_traces_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_731_; 
v_tid_706_ = lean_ctor_get_uint64(v_traceState_694_, sizeof(void*)*1);
v_traces_707_ = lean_ctor_get(v_traceState_694_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_traceState_694_);
if (v_isSharedCheck_731_ == 0)
{
v___x_709_ = v_traceState_694_;
v_isShared_710_ = v_isSharedCheck_731_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_traces_707_);
lean_dec(v_traceState_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_731_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; double v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_711_ = lean_box(0);
v___x_712_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_713_ = 0;
v___x_714_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_715_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_715_, 0, v_cls_680_);
lean_ctor_set(v___x_715_, 1, v___x_711_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
lean_ctor_set_float(v___x_715_, sizeof(void*)*3, v___x_712_);
lean_ctor_set_float(v___x_715_, sizeof(void*)*3 + 8, v___x_712_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 16, v___x_713_);
v___x_716_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_717_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v_a_689_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_inc(v_ref_687_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_ref_687_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_PersistentArray_push___redArg(v_traces_707_, v___x_718_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_719_);
v___x_721_ = v___x_709_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_719_);
lean_ctor_set_uint64(v_reuseFailAlloc_730_, sizeof(void*)*1, v_tid_706_);
v___x_721_ = v_reuseFailAlloc_730_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v___x_721_);
v___x_723_ = v___x_704_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_messages_700_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_infoState_701_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v_snapshotTasks_702_);
v___x_723_ = v_reuseFailAlloc_729_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = lean_st_ref_set(v___y_685_, v___x_723_);
v___x_725_ = lean_box(0);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_725_);
v___x_727_ = v___x_691_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_734_, v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
if (lean_obj_tag(v_as_745_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v_options_755_; uint8_t v_hasTrace_756_; 
v_options_755_ = lean_ctor_get(v___y_750_, 2);
v_hasTrace_756_ = lean_ctor_get_uint8(v_options_755_, sizeof(void*)*1);
if (v_hasTrace_756_ == 0)
{
lean_object* v_tail_757_; 
v_tail_757_ = lean_ctor_get(v_as_745_, 1);
lean_inc(v_tail_757_);
lean_dec_ref_known(v_as_745_, 2);
v_as_745_ = v_tail_757_;
goto _start;
}
else
{
lean_object* v_head_759_; lean_object* v_tail_760_; lean_object* v_fst_761_; lean_object* v_snd_762_; lean_object* v_inheritedTraceOptions_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_head_759_ = lean_ctor_get(v_as_745_, 0);
lean_inc(v_head_759_);
v_tail_760_ = lean_ctor_get(v_as_745_, 1);
lean_inc(v_tail_760_);
lean_dec_ref_known(v_as_745_, 2);
v_fst_761_ = lean_ctor_get(v_head_759_, 0);
lean_inc_n(v_fst_761_, 2);
v_snd_762_ = lean_ctor_get(v_head_759_, 1);
lean_inc(v_snd_762_);
lean_dec(v_head_759_);
v_inheritedTraceOptions_763_ = lean_ctor_get(v___y_750_, 13);
v___x_764_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_765_ = l_Lean_Name_append(v___x_764_, v_fst_761_);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_755_, v___x_765_);
lean_dec(v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_snd_762_);
lean_dec(v_fst_761_);
v_as_745_ = v_tail_760_;
goto _start;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_768_, 0, v_snd_762_);
v___x_769_ = l_Lean_MessageData_ofFormat(v___x_768_);
v___x_770_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_761_, v___x_769_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_dec_ref_known(v___x_770_, 1);
v_as_745_ = v_tail_760_;
goto _start;
}
else
{
lean_dec(v_tail_760_);
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v___x_783_; 
v___x_783_ = lean_box(0);
return v___x_783_;
}
else
{
lean_object* v_key_784_; lean_object* v_value_785_; lean_object* v_tail_786_; uint8_t v___x_787_; 
v_key_784_ = lean_ctor_get(v_x_782_, 0);
v_value_785_ = lean_ctor_get(v_x_782_, 1);
v_tail_786_ = lean_ctor_get(v_x_782_, 2);
v___x_787_ = lean_name_eq(v_key_784_, v_a_781_);
if (v___x_787_ == 0)
{
v_x_782_ = v_tail_786_;
goto _start;
}
else
{
lean_object* v___x_789_; 
lean_inc(v_value_785_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_value_785_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec(v_a_790_);
return v_res_792_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_793_; uint64_t v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(1723u);
v___x_794_ = lean_uint64_of_nat(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_buckets_797_; lean_object* v___x_798_; uint64_t v___y_800_; 
v_buckets_797_ = lean_ctor_get(v_m_795_, 1);
v___x_798_ = lean_array_get_size(v_buckets_797_);
if (lean_obj_tag(v_a_796_) == 0)
{
uint64_t v___x_814_; 
v___x_814_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_800_ = v___x_814_;
goto v___jp_799_;
}
else
{
uint64_t v_hash_815_; 
v_hash_815_ = lean_ctor_get_uint64(v_a_796_, sizeof(void*)*2);
v___y_800_ = v_hash_815_;
goto v___jp_799_;
}
v___jp_799_:
{
uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v_fold_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_801_ = 32ULL;
v___x_802_ = lean_uint64_shift_right(v___y_800_, v___x_801_);
v_fold_803_ = lean_uint64_xor(v___y_800_, v___x_802_);
v___x_804_ = 16ULL;
v___x_805_ = lean_uint64_shift_right(v_fold_803_, v___x_804_);
v___x_806_ = lean_uint64_xor(v_fold_803_, v___x_805_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = lean_usize_of_nat(v___x_798_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_sub(v___x_808_, v___x_809_);
v___x_811_ = lean_usize_land(v___x_807_, v___x_810_);
v___x_812_ = lean_array_uget_borrowed(v_buckets_797_, v___x_811_);
v___x_813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_796_, v___x_812_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_m_816_);
return v_res_818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_819_, lean_object* v_i_820_, lean_object* v_k_821_){
_start:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_array_get_size(v_keys_819_);
v___x_823_ = lean_nat_dec_lt(v_i_820_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v_i_820_);
return v___x_823_;
}
else
{
lean_object* v_k_x27_824_; uint8_t v___x_825_; 
v_k_x27_824_ = lean_array_fget_borrowed(v_keys_819_, v_i_820_);
v___x_825_ = l_Lean_instBEqExtraModUse_beq(v_k_821_, v_k_x27_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_add(v_i_820_, v___x_826_);
lean_dec(v_i_820_);
v_i_820_ = v___x_827_;
goto _start;
}
else
{
lean_dec(v_i_820_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_829_, v_i_830_, v_k_831_);
lean_dec_ref(v_k_831_);
lean_dec_ref(v_keys_829_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_834_, size_t v_x_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_es_837_; lean_object* v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v_j_841_; lean_object* v___x_842_; 
v_es_837_ = lean_ctor_get(v_x_834_, 0);
v___x_838_ = lean_box(2);
v___x_839_ = ((size_t)31ULL);
v___x_840_ = lean_usize_land(v_x_835_, v___x_839_);
v_j_841_ = lean_usize_to_nat(v___x_840_);
v___x_842_ = lean_array_get_borrowed(v___x_838_, v_es_837_, v_j_841_);
lean_dec(v_j_841_);
switch(lean_obj_tag(v___x_842_))
{
case 0:
{
lean_object* v_key_843_; uint8_t v___x_844_; 
v_key_843_ = lean_ctor_get(v___x_842_, 0);
v___x_844_ = l_Lean_instBEqExtraModUse_beq(v_x_836_, v_key_843_);
return v___x_844_;
}
case 1:
{
lean_object* v_node_845_; size_t v___x_846_; size_t v___x_847_; 
v_node_845_ = lean_ctor_get(v___x_842_, 0);
v___x_846_ = ((size_t)5ULL);
v___x_847_ = lean_usize_shift_right(v_x_835_, v___x_846_);
v_x_834_ = v_node_845_;
v_x_835_ = v___x_847_;
goto _start;
}
default: 
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
}
}
else
{
lean_object* v_ks_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_ks_850_ = lean_ctor_get(v_x_834_, 0);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_850_, v___x_851_, v_x_836_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
size_t v_x_281981__boxed_856_; uint8_t v_res_857_; lean_object* v_r_858_; 
v_x_281981__boxed_856_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_res_857_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_853_, v_x_281981__boxed_856_, v_x_855_);
lean_dec_ref(v_x_855_);
lean_dec_ref(v_x_853_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
uint64_t v___x_861_; size_t v___x_862_; uint8_t v___x_863_; 
v___x_861_ = l_Lean_instHashableExtraModUse_hash(v_x_860_);
v___x_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_859_, v___x_862_, v_x_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_864_, v_x_865_);
lean_dec_ref(v_x_865_);
lean_dec_ref(v_x_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_871_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_872_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_871_, v___x_870_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_879_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
lean_ctor_set(v___x_879_, 3, v___x_878_);
lean_ctor_set(v___x_879_, 4, v___x_878_);
lean_ctor_set(v___x_879_, 5, v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_cls_891_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_892_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_893_ = l_Lean_Name_append(v___x_892_, v_cls_891_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_904_, uint8_t v_isMeta_905_, lean_object* v_hint_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_env_915_; uint8_t v_isExporting_916_; lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v___x_919_; lean_object* v_entry_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; 
v___x_914_ = lean_st_ref_get(v___y_912_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
v_isExporting_916_ = lean_ctor_get_uint8(v_env_915_, sizeof(void*)*8);
lean_dec_ref(v_env_915_);
v___x_917_ = lean_st_ref_get(v___y_912_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_904_);
v_entry_920_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_920_, 0, v_mod_904_);
lean_ctor_set_uint8(v_entry_920_, sizeof(void*)*1, v_isExporting_916_);
lean_ctor_set_uint8(v_entry_920_, sizeof(void*)*1 + 1, v_isMeta_905_);
v___x_921_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_922_ = lean_box(1);
v___x_923_ = lean_box(0);
v___x_966_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_919_, v___x_921_, v_env_918_, v___x_922_, v___x_923_);
v___x_967_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_966_, v_entry_920_);
lean_dec(v___x_966_);
v___x_968_ = lean_bool_not(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref_known(v_entry_920_, 1);
lean_dec(v_hint_906_);
lean_dec(v_mod_904_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
else
{
lean_object* v_options_971_; uint8_t v_hasTrace_972_; 
v_options_971_ = lean_ctor_get(v___y_911_, 2);
v_hasTrace_972_ = lean_ctor_get_uint8(v_options_971_, sizeof(void*)*1);
if (v_hasTrace_972_ == 0)
{
lean_dec(v_hint_906_);
lean_dec(v_mod_904_);
v___y_925_ = v___y_910_;
v___y_926_ = v___y_912_;
goto v___jp_924_;
}
else
{
lean_object* v_inheritedTraceOptions_973_; lean_object* v_cls_974_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_inheritedTraceOptions_973_ = lean_ctor_get(v___y_911_, 13);
v_cls_974_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_994_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_995_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_973_, v_options_971_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec(v_hint_906_);
lean_dec(v_mod_904_);
v___y_925_ = v___y_910_;
v___y_926_ = v___y_912_;
goto v___jp_924_;
}
else
{
lean_object* v___x_996_; lean_object* v___y_998_; 
v___x_996_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_916_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_998_ = v___x_1005_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_998_ = v___x_1006_;
goto v___jp_997_;
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v___y_998_);
v___x_999_ = l_Lean_stringToMessageData(v___y_998_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_996_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
if (v_isMeta_905_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1003_;
goto v___jp_980_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1004_;
goto v___jp_980_;
}
}
}
v___jp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___y_976_);
lean_ctor_set(v___x_978_, 1, v___y_977_);
v___x_979_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_974_, v___x_978_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref_known(v___x_979_, 1);
v___y_925_ = v___y_910_;
v___y_926_ = v___y_912_;
goto v___jp_924_;
}
else
{
lean_dec_ref_known(v_entry_920_, 1);
return v___x_979_;
}
}
v___jp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
lean_inc_ref(v___y_982_);
v___x_983_ = l_Lean_stringToMessageData(v___y_982_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___y_981_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_MessageData_ofName(v_mod_904_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_Name_isAnonymous(v_hint_906_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_991_ = l_Lean_MessageData_ofName(v_hint_906_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___y_976_ = v___x_988_;
v___y_977_ = v___x_992_;
goto v___jp_975_;
}
else
{
lean_object* v___x_993_; 
lean_dec(v_hint_906_);
v___x_993_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_976_ = v___x_988_;
v___y_977_ = v___x_993_;
goto v___jp_975_;
}
}
}
}
v___jp_924_:
{
lean_object* v___x_927_; lean_object* v_toEnvExtension_928_; lean_object* v_env_929_; lean_object* v_nextMacroScope_930_; lean_object* v_ngen_931_; lean_object* v_auxDeclNGen_932_; lean_object* v_traceState_933_; lean_object* v_messages_934_; lean_object* v_infoState_935_; lean_object* v_snapshotTasks_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_964_; 
v___x_927_ = lean_st_ref_take(v___y_926_);
v_toEnvExtension_928_ = lean_ctor_get(v___x_921_, 0);
v_env_929_ = lean_ctor_get(v___x_927_, 0);
v_nextMacroScope_930_ = lean_ctor_get(v___x_927_, 1);
v_ngen_931_ = lean_ctor_get(v___x_927_, 2);
v_auxDeclNGen_932_ = lean_ctor_get(v___x_927_, 3);
v_traceState_933_ = lean_ctor_get(v___x_927_, 4);
v_messages_934_ = lean_ctor_get(v___x_927_, 6);
v_infoState_935_ = lean_ctor_get(v___x_927_, 7);
v_snapshotTasks_936_ = lean_ctor_get(v___x_927_, 8);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_927_, 5);
lean_dec(v_unused_965_);
v___x_938_ = v___x_927_;
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snapshotTasks_936_);
lean_inc(v_infoState_935_);
lean_inc(v_messages_934_);
lean_inc(v_traceState_933_);
lean_inc(v_auxDeclNGen_932_);
lean_inc(v_ngen_931_);
lean_inc(v_nextMacroScope_930_);
lean_inc(v_env_929_);
lean_dec(v___x_927_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_964_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_asyncMode_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_asyncMode_940_ = lean_ctor_get(v_toEnvExtension_928_, 2);
v___x_941_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_921_, v_env_929_, v_entry_920_, v_asyncMode_940_, v___x_923_);
v___x_942_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 5, v___x_942_);
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_nextMacroScope_930_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_ngen_931_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_auxDeclNGen_932_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_traceState_933_);
lean_ctor_set(v_reuseFailAlloc_963_, 5, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_963_, 6, v_messages_934_);
lean_ctor_set(v_reuseFailAlloc_963_, 7, v_infoState_935_);
lean_ctor_set(v_reuseFailAlloc_963_, 8, v_snapshotTasks_936_);
v___x_944_ = v_reuseFailAlloc_963_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_mctx_947_; lean_object* v_zetaDeltaFVarIds_948_; lean_object* v_postponed_949_; lean_object* v_diag_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_961_; 
v___x_945_ = lean_st_ref_set(v___y_926_, v___x_944_);
v___x_946_ = lean_st_ref_take(v___y_925_);
v_mctx_947_ = lean_ctor_get(v___x_946_, 0);
v_zetaDeltaFVarIds_948_ = lean_ctor_get(v___x_946_, 2);
v_postponed_949_ = lean_ctor_get(v___x_946_, 3);
v_diag_950_ = lean_ctor_get(v___x_946_, 4);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_946_, 1);
lean_dec(v_unused_962_);
v___x_952_ = v___x_946_;
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_diag_950_);
lean_inc(v_postponed_949_);
lean_inc(v_zetaDeltaFVarIds_948_);
lean_inc(v_mctx_947_);
lean_dec(v___x_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_mctx_947_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_zetaDeltaFVarIds_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_postponed_949_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_diag_950_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_st_ref_set(v___y_925_, v___x_956_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1007_, lean_object* v_isMeta_1008_, lean_object* v_hint_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v_isMeta_boxed_1017_; lean_object* v_res_1018_; 
v_isMeta_boxed_1017_ = lean_unbox(v_isMeta_1008_);
v_res_1018_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1007_, v_isMeta_boxed_1017_, v_hint_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1019_, lean_object* v_declName_1020_, lean_object* v_as_1021_, size_t v_sz_1022_, size_t v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_lt(v_i_1023_, v_sz_1022_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec(v_declName_1020_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_b_1024_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v_modules_1035_; lean_object* v___x_1036_; lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v_toImport_1039_; lean_object* v_module_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1034_ = l_Lean_Environment_header(v___x_1019_);
v_modules_1035_ = lean_ctor_get(v___x_1034_, 3);
lean_inc_ref(v_modules_1035_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1037_ = lean_array_uget_borrowed(v_as_1021_, v_i_1023_);
v___x_1038_ = lean_array_get(v___x_1036_, v_modules_1035_, v_a_1037_);
lean_dec_ref(v_modules_1035_);
v_toImport_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_toImport_1039_);
lean_dec(v___x_1038_);
v_module_1040_ = lean_ctor_get(v_toImport_1039_, 0);
lean_inc(v_module_1040_);
lean_dec_ref(v_toImport_1039_);
v___x_1041_ = 0;
lean_inc(v_declName_1020_);
v___x_1042_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1040_, v___x_1041_, v_declName_1020_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; 
lean_dec_ref_known(v___x_1042_, 1);
v___x_1043_ = lean_box(0);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1023_, v___x_1044_);
v_i_1023_ = v___x_1045_;
v_b_1024_ = v___x_1043_;
goto _start;
}
else
{
lean_dec(v_declName_1020_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1047_, lean_object* v_declName_1048_, lean_object* v_as_1049_, lean_object* v_sz_1050_, lean_object* v_i_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
size_t v_sz_boxed_1060_; size_t v_i_boxed_1061_; lean_object* v_res_1062_; 
v_sz_boxed_1060_ = lean_unbox_usize(v_sz_1050_);
lean_dec(v_sz_1050_);
v_i_boxed_1061_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1047_, v_declName_1048_, v_as_1049_, v_sz_boxed_1060_, v_i_boxed_1061_, v_b_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v_as_1049_);
lean_dec_ref(v___x_1047_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1066_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1067_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1066_, v___x_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1070_, uint8_t v_isMeta_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_env_1083_; lean_object* v___y_1085_; lean_object* v___x_1098_; 
v___x_1079_ = lean_st_ref_get(v___y_1077_);
v_env_1083_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1079_);
v___x_1098_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1083_, v_declName_1070_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref(v_env_1083_);
lean_dec(v_declName_1070_);
goto v___jp_1080_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1100_; lean_object* v_modules_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_val_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = l_Lean_Environment_header(v_env_1083_);
v_modules_1101_ = lean_ctor_get(v___x_1100_, 3);
lean_inc_ref(v_modules_1101_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = lean_array_get_size(v_modules_1101_);
v___x_1103_ = lean_nat_dec_lt(v_val_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_modules_1101_);
lean_dec(v_val_1099_);
lean_dec_ref(v_env_1083_);
lean_dec(v_declName_1070_);
goto v___jp_1080_;
}
else
{
lean_object* v___x_1104_; lean_object* v_env_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___y_1109_; 
v___x_1104_ = lean_st_ref_get(v___y_1077_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1107_ = lean_array_fget(v_modules_1101_, v_val_1099_);
lean_dec(v_val_1099_);
lean_dec_ref(v_modules_1101_);
if (v_isMeta_1071_ == 0)
{
lean_dec_ref(v_env_1105_);
v___y_1109_ = v_isMeta_1071_;
goto v___jp_1108_;
}
else
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
lean_inc(v_declName_1070_);
v___x_1120_ = l_Lean_isMarkedMeta(v_env_1105_, v_declName_1070_);
v___x_1121_ = lean_bool_not(v___x_1120_);
v___y_1109_ = v___x_1121_;
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v_toImport_1110_; lean_object* v_module_1111_; lean_object* v___x_1112_; 
v_toImport_1110_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_toImport_1110_);
lean_dec(v___x_1107_);
v_module_1111_ = lean_ctor_get(v_toImport_1110_, 0);
lean_inc(v_module_1111_);
lean_dec_ref(v_toImport_1110_);
lean_inc(v_declName_1070_);
v___x_1112_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1111_, v___y_1109_, v_declName_1070_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1113_ = l_Lean_indirectModUseExt;
v___x_1114_ = lean_box(1);
v___x_1115_ = lean_box(0);
lean_inc_ref(v_env_1083_);
v___x_1116_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1106_, v___x_1113_, v_env_1083_, v___x_1114_, v___x_1115_);
v___x_1117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1116_, v_declName_1070_);
lean_dec(v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1085_ = v___x_1118_;
goto v___jp_1084_;
}
else
{
lean_object* v_val_1119_; 
v_val_1119_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v___x_1117_, 1);
v___y_1085_ = v_val_1119_;
goto v___jp_1084_;
}
}
else
{
lean_dec_ref(v_env_1083_);
lean_dec(v_declName_1070_);
return v___x_1112_;
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = lean_box(0);
v_sz_1087_ = lean_array_size(v___y_1085_);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1083_, v_declName_1070_, v___y_1085_, v_sz_1087_, v___x_1088_, v___x_1086_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_env_1083_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1097_);
v___x_1091_ = v___x_1089_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1086_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1086_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1122_, lean_object* v_isMeta_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_isMeta_boxed_1131_; lean_object* v_res_1132_; 
v_isMeta_boxed_1131_ = lean_unbox(v_isMeta_1123_);
v_res_1132_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1122_, v_isMeta_boxed_1131_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
if (lean_obj_tag(v_as_x27_1133_) == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_b_1134_);
return v___x_1142_;
}
else
{
lean_object* v_head_1143_; lean_object* v_tail_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; 
v_head_1143_ = lean_ctor_get(v_as_x27_1133_, 0);
v_tail_1144_ = lean_ctor_get(v_as_x27_1133_, 1);
v___x_1145_ = 1;
lean_inc(v_head_1143_);
v___x_1146_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1143_, v___x_1145_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1146_, 1);
v___x_1147_ = lean_box(0);
v_as_x27_1133_ = v_tail_1144_;
v_b_1134_ = v___x_1147_;
goto _start;
}
else
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1149_, v_b_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v_as_x27_1149_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1159_, lean_object* v_currNamespace_1160_, lean_object* v_openDecls_1161_, lean_object* v_n_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Lean_ResolveName_resolveNamespace(v_env_1159_, v_currNamespace_1160_, v_openDecls_1161_, v_n_1162_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___y_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1167_, lean_object* v_currNamespace_1168_, lean_object* v_openDecls_1169_, lean_object* v_n_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1167_, v_currNamespace_1168_, v_openDecls_1169_, v_n_1170_, v___y_1171_, v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_currNamespace_1174_);
lean_ctor_set(v___x_1177_, 1, v___y_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1182_, lean_object* v_options_1183_, lean_object* v_currNamespace_1184_, lean_object* v_openDecls_1185_, lean_object* v_n_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = l_Lean_ResolveName_resolveGlobalName(v_env_1182_, v_options_1183_, v_currNamespace_1184_, v_openDecls_1185_, v_n_1186_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1191_, lean_object* v_options_1192_, lean_object* v_currNamespace_1193_, lean_object* v_openDecls_1194_, lean_object* v_n_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1191_, v_options_1192_, v_currNamespace_1193_, v_openDecls_1194_, v_n_1195_, v___y_1196_, v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_options_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v_env_1209_; lean_object* v_options_1210_; lean_object* v_currRecDepth_1211_; lean_object* v_maxRecDepth_1212_; lean_object* v_ref_1213_; lean_object* v_currNamespace_1214_; lean_object* v_openDecls_1215_; lean_object* v_quotContext_1216_; lean_object* v_currMacroScope_1217_; lean_object* v___x_1218_; lean_object* v_nextMacroScope_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v_methods_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1208_ = lean_st_ref_get(v___y_1206_);
v_env_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc_ref_n(v_env_1209_, 4);
lean_dec(v___x_1208_);
v_options_1210_ = lean_ctor_get(v___y_1205_, 2);
v_currRecDepth_1211_ = lean_ctor_get(v___y_1205_, 3);
v_maxRecDepth_1212_ = lean_ctor_get(v___y_1205_, 4);
v_ref_1213_ = lean_ctor_get(v___y_1205_, 5);
v_currNamespace_1214_ = lean_ctor_get(v___y_1205_, 6);
v_openDecls_1215_ = lean_ctor_get(v___y_1205_, 7);
v_quotContext_1216_ = lean_ctor_get(v___y_1205_, 10);
v_currMacroScope_1217_ = lean_ctor_get(v___y_1205_, 11);
v___x_1218_ = lean_st_ref_get(v___y_1206_);
v_nextMacroScope_1219_ = lean_ctor_get(v___x_1218_, 1);
lean_inc(v_nextMacroScope_1219_);
lean_dec(v___x_1218_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1220_, 0, v_env_1209_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1221_, 0, v_env_1209_);
lean_inc_n(v_openDecls_1215_, 2);
lean_inc_n(v_currNamespace_1214_, 3);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1222_, 0, v_env_1209_);
lean_closure_set(v___f_1222_, 1, v_currNamespace_1214_);
lean_closure_set(v___f_1222_, 2, v_openDecls_1215_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1223_, 0, v_currNamespace_1214_);
lean_inc_ref(v_options_1210_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1224_, 0, v_env_1209_);
lean_closure_set(v___f_1224_, 1, v_options_1210_);
lean_closure_set(v___f_1224_, 2, v_currNamespace_1214_);
lean_closure_set(v___f_1224_, 3, v_openDecls_1215_);
v_methods_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1225_, 0, v___f_1220_);
lean_ctor_set(v_methods_1225_, 1, v___f_1223_);
lean_ctor_set(v_methods_1225_, 2, v___f_1221_);
lean_ctor_set(v_methods_1225_, 3, v___f_1222_);
lean_ctor_set(v_methods_1225_, 4, v___f_1224_);
lean_inc(v_ref_1213_);
lean_inc(v_maxRecDepth_1212_);
lean_inc(v_currRecDepth_1211_);
lean_inc(v_currMacroScope_1217_);
lean_inc(v_quotContext_1216_);
v___x_1226_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1226_, 0, v_methods_1225_);
lean_ctor_set(v___x_1226_, 1, v_quotContext_1216_);
lean_ctor_set(v___x_1226_, 2, v_currMacroScope_1217_);
lean_ctor_set(v___x_1226_, 3, v_currRecDepth_1211_);
lean_ctor_set(v___x_1226_, 4, v_maxRecDepth_1212_);
lean_ctor_set(v___x_1226_, 5, v_ref_1213_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1228_, 0, v_nextMacroScope_1219_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
lean_ctor_set(v___x_1228_, 2, v___x_1227_);
v___x_1229_ = lean_apply_2(v_x_1200_, v___x_1226_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v_a_1231_; lean_object* v_macroScope_1232_; lean_object* v_traceMsgs_1233_; lean_object* v_expandedMacroDecls_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 1);
lean_inc(v_a_1230_);
v_a_1231_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1229_, 2);
v_macroScope_1232_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_macroScope_1232_);
v_traceMsgs_1233_ = lean_ctor_get(v_a_1230_, 1);
lean_inc(v_traceMsgs_1233_);
v_expandedMacroDecls_1234_ = lean_ctor_get(v_a_1230_, 2);
lean_inc(v_expandedMacroDecls_1234_);
lean_dec(v_a_1230_);
v___x_1235_ = lean_box(0);
v___x_1236_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1234_, v___x_1235_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v_expandedMacroDecls_1234_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; lean_object* v_env_1238_; lean_object* v_ngen_1239_; lean_object* v_auxDeclNGen_1240_; lean_object* v_traceState_1241_; lean_object* v_cache_1242_; lean_object* v_messages_1243_; lean_object* v_infoState_1244_; lean_object* v_snapshotTasks_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref_known(v___x_1236_, 1);
v___x_1237_ = lean_st_ref_take(v___y_1206_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
v_ngen_1239_ = lean_ctor_get(v___x_1237_, 2);
v_auxDeclNGen_1240_ = lean_ctor_get(v___x_1237_, 3);
v_traceState_1241_ = lean_ctor_get(v___x_1237_, 4);
v_cache_1242_ = lean_ctor_get(v___x_1237_, 5);
v_messages_1243_ = lean_ctor_get(v___x_1237_, 6);
v_infoState_1244_ = lean_ctor_get(v___x_1237_, 7);
v_snapshotTasks_1245_ = lean_ctor_get(v___x_1237_, 8);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1237_, 1);
lean_dec(v_unused_1272_);
v___x_1247_ = v___x_1237_;
v_isShared_1248_ = v_isSharedCheck_1271_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snapshotTasks_1245_);
lean_inc(v_infoState_1244_);
lean_inc(v_messages_1243_);
lean_inc(v_cache_1242_);
lean_inc(v_traceState_1241_);
lean_inc(v_auxDeclNGen_1240_);
lean_inc(v_ngen_1239_);
lean_inc(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1271_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_macroScope_1232_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_env_1238_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_macroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_ngen_1239_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_auxDeclNGen_1240_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_traceState_1241_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_cache_1242_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_messages_1243_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_infoState_1244_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_snapshotTasks_1245_);
v___x_1250_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_st_ref_set(v___y_1206_, v___x_1250_);
v___x_1252_ = l_List_reverse___redArg(v_traceMsgs_1233_);
v___x_1253_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1252_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1261_);
v___x_1255_ = v___x_1253_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v___x_1253_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v_a_1231_);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1231_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_a_1231_);
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1253_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1253_);
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
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_traceMsgs_1233_);
lean_dec(v_macroScope_1232_);
lean_dec(v_a_1231_);
v_a_1273_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1236_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1236_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; 
v_a_1281_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1229_, 2);
if (lean_obj_tag(v_a_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v_a_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_a_1282_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_a_1282_);
v_a_1283_ = lean_ctor_get(v_a_1281_, 1);
lean_inc_ref(v_a_1283_);
lean_dec_ref_known(v_a_1281_, 2);
v___x_1284_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1285_ = lean_string_dec_eq(v_a_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1283_);
v___x_1287_ = l_Lean_MessageData_ofFormat(v___x_1286_);
v___x_1288_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1282_, v___x_1287_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v_a_1282_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v_a_1283_);
v___x_1289_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1282_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_bs_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_bs_1305_);
return v___x_1307_;
}
else
{
lean_object* v_v_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_v_1308_ = lean_array_uget(v_bs_1305_, v_i_1304_);
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1308_);
v___x_1310_ = l_Lean_Syntax_isOfKind(v_v_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_v_1308_);
lean_dec_ref(v_bs_1305_);
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Lean_Syntax_getArg(v_v_1308_, v___x_1312_);
v___x_1314_ = l_Lean_Syntax_isOfKind(v___x_1313_, v___x_1309_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_v_1308_);
lean_dec_ref(v_bs_1305_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v_bs_x27_1317_; lean_object* v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = lean_unsigned_to_nat(3u);
v_bs_x27_1317_ = lean_array_uset(v_bs_1305_, v_i_1304_, v___x_1312_);
v___x_1318_ = l_Lean_Syntax_getArg(v_v_1308_, v___x_1316_);
lean_dec(v_v_1308_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1304_, v___x_1319_);
v___x_1321_ = lean_array_uset(v_bs_x27_1317_, v_i_1304_, v___x_1318_);
v_i_1304_ = v___x_1320_;
v_bs_1305_ = v___x_1321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_bs_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1326_, v_i_boxed_1327_, v_bs_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_bs_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_bs_1343_);
return v___x_1345_;
}
else
{
lean_object* v_v_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_v_1346_ = lean_array_uget(v_bs_1343_, v_i_1342_);
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1346_);
v___x_1348_ = l_Lean_Syntax_isOfKind(v_v_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec(v_v_1346_);
lean_dec_ref(v_bs_1343_);
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = l_Lean_Syntax_getArg(v_v_1346_, v___x_1350_);
v___x_1352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1353_ = l_Lean_Syntax_isOfKind(v___x_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec(v_v_1346_);
lean_dec_ref(v_bs_1343_);
v___x_1354_ = lean_box(0);
return v___x_1354_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_bs_x27_1357_; lean_object* v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1355_ = lean_unsigned_to_nat(3u);
v___x_1356_ = lean_unsigned_to_nat(0u);
v_bs_x27_1357_ = lean_array_uset(v_bs_1343_, v_i_1342_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_getArg(v_v_1346_, v___x_1355_);
lean_dec(v_v_1346_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1342_, v___x_1359_);
v___x_1361_ = lean_array_uset(v_bs_x27_1357_, v_i_1342_, v___x_1358_);
v_i_1342_ = v___x_1360_;
v_bs_1343_ = v___x_1361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1363_, lean_object* v_i_1364_, lean_object* v_bs_1365_){
_start:
{
size_t v_sz_boxed_1366_; size_t v_i_boxed_1367_; lean_object* v_res_1368_; 
v_sz_boxed_1366_ = lean_unbox_usize(v_sz_1363_);
lean_dec(v_sz_1363_);
v_i_boxed_1367_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1366_, v_i_boxed_1367_, v_bs_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_bs_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1376_, v_sz_1375_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_bs_1377_);
return v___x_1379_;
}
else
{
lean_object* v_v_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_v_1380_ = lean_array_uget(v_bs_1377_, v_i_1376_);
v___x_1381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1380_);
v___x_1382_ = l_Lean_Syntax_isOfKind(v_v_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec(v_v_1380_);
lean_dec_ref(v_bs_1377_);
v___x_1383_ = lean_box(0);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v_bs_x27_1385_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v_bs_x27_1385_ = lean_array_uset(v_bs_1377_, v_i_1376_, v___x_1384_);
v___x_1392_ = l_Lean_Syntax_getArg(v_v_1380_, v___x_1384_);
lean_dec(v_v_1380_);
v___x_1393_ = l_Lean_Syntax_isNone(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_unsigned_to_nat(2u);
v___x_1395_ = l_Lean_Syntax_matchesNull(v___x_1392_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_bs_x27_1385_);
v___x_1396_ = lean_box(0);
return v___x_1396_;
}
else
{
goto v___jp_1386_;
}
}
else
{
lean_dec(v___x_1392_);
goto v___jp_1386_;
}
v___jp_1386_:
{
lean_object* v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1376_, v___x_1388_);
v___x_1390_ = lean_array_uset(v_bs_x27_1385_, v_i_1376_, v___x_1387_);
v_i_1376_ = v___x_1389_;
v_bs_1377_ = v___x_1390_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_bs_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1400_, v_i_boxed_1401_, v_bs_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1403_, size_t v_i_1404_, lean_object* v_bs_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_bs_1405_);
return v___x_1407_;
}
else
{
lean_object* v_v_1408_; lean_object* v___x_1409_; lean_object* v_bs_x27_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v_v_1408_ = lean_array_uget(v_bs_1405_, v_i_1404_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v_bs_x27_1410_ = lean_array_uset(v_bs_1405_, v_i_1404_, v___x_1409_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1404_, v___x_1411_);
v___x_1413_ = lean_array_uset(v_bs_x27_1410_, v_i_1404_, v_v_1408_);
v_i_1404_ = v___x_1412_;
v_bs_1405_ = v___x_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_bs_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1418_, v_i_boxed_1419_, v_bs_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1422_, v___y_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1426_, v_x_1427_, v___y_1428_, v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_x_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1434_, lean_object* v_as_x27_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
if (lean_obj_tag(v_as_x27_1435_) == 0)
{
lean_object* v___x_1444_; 
lean_dec(v_stx_1434_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_b_1436_);
return v___x_1444_;
}
else
{
lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v_value_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_b_1436_);
v_head_1445_ = lean_ctor_get(v_as_x27_1435_, 0);
v_tail_1446_ = lean_ctor_get(v_as_x27_1435_, 1);
v_value_1447_ = lean_ctor_get(v_head_1445_, 1);
v___x_1448_ = lean_box(0);
lean_inc(v_value_1447_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v_stx_1434_);
v___x_1449_ = lean_apply_8(v_value_1447_, v_stx_1434_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_stx_1434_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1450_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1448_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1482_; 
v_a_1460_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1462_ = v___x_1449_;
v_isShared_1463_ = v_isSharedCheck_1482_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1449_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1482_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___y_1467_; uint8_t v___x_1480_; 
v___x_1464_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1465_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1480_ = l_Lean_Exception_isInterrupt(v_a_1460_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
lean_inc(v_a_1460_);
v___x_1481_ = l_Lean_Exception_isRuntime(v_a_1460_);
v___y_1467_ = v___x_1481_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___x_1480_;
goto v___jp_1466_;
}
v___jp_1466_:
{
if (v___y_1467_ == 0)
{
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_stx_1434_);
if (v_isShared_1463_ == 0)
{
v___x_1469_ = v___x_1462_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1460_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
else
{
lean_object* v_id_1471_; uint8_t v___x_1472_; 
v_id_1471_ = lean_ctor_get(v_a_1460_, 0);
v___x_1472_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1465_, v_id_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1474_; 
lean_dec(v_stx_1434_);
if (v_isShared_1463_ == 0)
{
v___x_1474_ = v___x_1462_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1460_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_dec_ref_known(v_a_1460_, 2);
lean_del_object(v___x_1462_);
v_as_x27_1435_ = v_tail_1446_;
v_b_1436_ = v___x_1464_;
goto _start;
}
}
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_stx_1434_);
if (v_isShared_1463_ == 0)
{
v___x_1478_ = v___x_1462_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1460_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1483_, lean_object* v_as_x27_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1483_, v_as_x27_1484_, v_b_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v_as_x27_1484_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1496_, lean_object* v_rhs_x3f_1497_, lean_object* v_otherwise_x3f_1498_, lean_object* v_body_x3f_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
uint8_t v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; uint8_t v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v_body_1519_; lean_object* v___y_1540_; lean_object* v_otherwise_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_rhs_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; 
if (lean_obj_tag(v_rhs_x3f_1497_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1553_ = v___x_1564_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
v___y_1558_ = v_a_1504_;
v___y_1559_ = v_a_1505_;
goto v___jp_1552_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1566_; 
v_val_1565_ = lean_ctor_get(v_rhs_x3f_1497_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v_rhs_x3f_1497_, 1);
v___x_1566_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1565_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v_rhs_1553_ = v_a_1567_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
v___y_1558_ = v_a_1504_;
v___y_1559_ = v_a_1505_;
goto v___jp_1552_;
}
else
{
lean_dec(v_body_x3f_1499_);
lean_dec(v_otherwise_x3f_1498_);
lean_dec_ref(v_reassigned_1496_);
return v___x_1566_;
}
}
v___jp_1507_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1514_, 0, v___y_1509_);
lean_ctor_set(v___x_1514_, 1, v___y_1513_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*2, v___y_1510_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*2 + 1, v___y_1512_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*2 + 2, v___y_1511_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*2 + 3, v___y_1508_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
v___jp_1516_:
{
lean_object* v___x_1520_; lean_object* v_info_1521_; uint8_t v_breaks_1522_; uint8_t v_continues_1523_; uint8_t v_returnsEarly_1524_; lean_object* v_numRegularExits_1525_; uint8_t v_noFallthrough_1526_; lean_object* v_reassigns_1527_; size_t v_sz_1528_; size_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1520_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1519_, v___y_1518_);
v_info_1521_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1517_, v___x_1520_);
v_breaks_1522_ = lean_ctor_get_uint8(v_info_1521_, sizeof(void*)*2);
v_continues_1523_ = lean_ctor_get_uint8(v_info_1521_, sizeof(void*)*2 + 1);
v_returnsEarly_1524_ = lean_ctor_get_uint8(v_info_1521_, sizeof(void*)*2 + 2);
v_numRegularExits_1525_ = lean_ctor_get(v_info_1521_, 0);
lean_inc(v_numRegularExits_1525_);
v_noFallthrough_1526_ = lean_ctor_get_uint8(v_info_1521_, sizeof(void*)*2 + 3);
v_reassigns_1527_ = lean_ctor_get(v_info_1521_, 1);
lean_inc(v_reassigns_1527_);
lean_dec_ref(v_info_1521_);
v_sz_1528_ = lean_array_size(v_reassigned_1496_);
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1528_, v___x_1529_, v_reassigned_1496_);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_array_get_size(v___x_1530_);
v___x_1533_ = lean_nat_dec_lt(v___x_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec_ref(v___x_1530_);
v___y_1508_ = v_noFallthrough_1526_;
v___y_1509_ = v_numRegularExits_1525_;
v___y_1510_ = v_breaks_1522_;
v___y_1511_ = v_returnsEarly_1524_;
v___y_1512_ = v_continues_1523_;
v___y_1513_ = v_reassigns_1527_;
goto v___jp_1507_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_le(v___x_1532_, v___x_1532_);
if (v___x_1534_ == 0)
{
if (v___x_1533_ == 0)
{
lean_dec_ref(v___x_1530_);
v___y_1508_ = v_noFallthrough_1526_;
v___y_1509_ = v_numRegularExits_1525_;
v___y_1510_ = v_breaks_1522_;
v___y_1511_ = v_returnsEarly_1524_;
v___y_1512_ = v_continues_1523_;
v___y_1513_ = v_reassigns_1527_;
goto v___jp_1507_;
}
else
{
size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_usize_of_nat(v___x_1532_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1530_, v___x_1529_, v___x_1535_, v_reassigns_1527_);
lean_dec_ref(v___x_1530_);
v___y_1508_ = v_noFallthrough_1526_;
v___y_1509_ = v_numRegularExits_1525_;
v___y_1510_ = v_breaks_1522_;
v___y_1511_ = v_returnsEarly_1524_;
v___y_1512_ = v_continues_1523_;
v___y_1513_ = v___x_1536_;
goto v___jp_1507_;
}
}
else
{
size_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_usize_of_nat(v___x_1532_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1530_, v___x_1529_, v___x_1537_, v_reassigns_1527_);
lean_dec_ref(v___x_1530_);
v___y_1508_ = v_noFallthrough_1526_;
v___y_1509_ = v_numRegularExits_1525_;
v___y_1510_ = v_breaks_1522_;
v___y_1511_ = v_returnsEarly_1524_;
v___y_1512_ = v_continues_1523_;
v___y_1513_ = v___x_1538_;
goto v___jp_1507_;
}
}
}
v___jp_1539_:
{
if (lean_obj_tag(v_body_x3f_1499_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1517_ = v___y_1540_;
v___y_1518_ = v_otherwise_1541_;
v_body_1519_ = v___x_1548_;
goto v___jp_1516_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1550_; 
v_val_1549_ = lean_ctor_get(v_body_x3f_1499_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_body_x3f_1499_, 1);
v___x_1550_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1549_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___y_1517_ = v___y_1540_;
v___y_1518_ = v_otherwise_1541_;
v_body_1519_ = v_a_1551_;
goto v___jp_1516_;
}
else
{
lean_dec_ref(v_otherwise_1541_);
lean_dec_ref(v___y_1540_);
lean_dec_ref(v_reassigned_1496_);
return v___x_1550_;
}
}
}
v___jp_1552_:
{
if (lean_obj_tag(v_otherwise_x3f_1498_) == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1540_ = v_rhs_1553_;
v_otherwise_1541_ = v___x_1560_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
goto v___jp_1539_;
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1562_; 
v_val_1561_ = lean_ctor_get(v_otherwise_x3f_1498_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_otherwise_x3f_1498_, 1);
v___x_1562_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1561_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___y_1540_ = v_rhs_1553_;
v_otherwise_1541_ = v_a_1563_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
goto v___jp_1539_;
}
else
{
lean_dec_ref(v_rhs_1553_);
lean_dec(v_body_x3f_1499_);
lean_dec_ref(v_reassigned_1496_);
return v___x_1562_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1670_, lean_object* v_decl_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v_reassigns_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1671_);
v___x_1708_ = l_Lean_Syntax_isOfKind(v_decl_1671_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1671_);
v___x_1710_ = l_Lean_Syntax_isOfKind(v_decl_1671_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1712_ = lean_box(0);
v___x_1713_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1712_, v___x_1710_);
v___x_1714_ = l_Std_Format_defWidth;
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = l_Std_Format_pretty(v___x_1713_, v___x_1714_, v___x_1715_, v___x_1715_);
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1711_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1718_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v_pattern_1721_; lean_object* v___y_1723_; lean_object* v_otherwise_x3f_1724_; lean_object* v_body_x3f_x3f_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v_body_x3f_x3f_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___x_1755_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1720_ = lean_unsigned_to_nat(0u);
v_pattern_1721_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1720_);
v___x_1755_ = lean_unsigned_to_nat(1u);
v___x_1794_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1755_);
v___x_1795_ = l_Lean_Syntax_isNone(v___x_1794_);
if (v___x_1795_ == 0)
{
uint8_t v___x_1796_; 
lean_inc(v___x_1794_);
v___x_1796_ = l_Lean_Syntax_matchesNull(v___x_1794_, v___x_1755_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v___x_1794_);
lean_dec(v_pattern_1721_);
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1798_ = lean_box(0);
v___x_1799_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1798_, v___x_1796_);
v___x_1800_ = l_Std_Format_defWidth;
v___x_1801_ = l_Std_Format_pretty(v___x_1799_, v___x_1800_, v___x_1720_, v___x_1720_);
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1797_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1803_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = l_Lean_Syntax_getArg(v___x_1794_, v___x_1720_);
lean_dec(v___x_1794_);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1807_ = l_Lean_Syntax_isOfKind(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v_pattern_1721_);
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1809_, v___x_1807_);
v___x_1811_ = l_Std_Format_defWidth;
v___x_1812_ = l_Std_Format_pretty(v___x_1810_, v___x_1811_, v___x_1720_, v___x_1720_);
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1808_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1814_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1815_;
}
else
{
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
v___y_1761_ = v_a_1676_;
v___y_1762_ = v_a_1677_;
goto v___jp_1756_;
}
}
}
else
{
lean_dec(v___x_1794_);
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
v___y_1761_ = v_a_1676_;
v___y_1762_ = v_a_1677_;
goto v___jp_1756_;
}
v___jp_1722_:
{
if (v_reassignment_1670_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v_pattern_1721_);
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1692_ = v_otherwise_x3f_1724_;
v___y_1693_ = v___y_1723_;
v___y_1694_ = v_body_x3f_x3f_1725_;
v_reassigns_1695_ = v___x_1732_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1731_;
goto v___jp_1691_;
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1721_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___y_1692_ = v_otherwise_x3f_1724_;
v___y_1693_ = v___y_1723_;
v___y_1694_ = v_body_x3f_x3f_1725_;
v_reassigns_1695_ = v_a_1734_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1731_;
goto v___jp_1691_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_body_x3f_x3f_1725_);
lean_dec(v_otherwise_x3f_1724_);
lean_dec(v___y_1723_);
v_a_1735_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1733_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
v___jp_1743_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___y_1745_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_body_x3f_x3f_1746_);
v___y_1723_ = v___y_1744_;
v_otherwise_x3f_1724_ = v___x_1753_;
v_body_x3f_x3f_1725_ = v___x_1754_;
v___y_1726_ = v___y_1747_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1749_;
v___y_1729_ = v___y_1750_;
v___y_1730_ = v___y_1751_;
v___y_1731_ = v___y_1752_;
goto v___jp_1722_;
}
v___jp_1756_:
{
lean_object* v___x_1763_; lean_object* v_rhs_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1763_ = lean_unsigned_to_nat(3u);
v_rhs_1764_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1763_);
v___x_1765_ = lean_unsigned_to_nat(4u);
v___x_1766_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1765_);
v___x_1767_ = l_Lean_Syntax_isNone(v___x_1766_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; 
lean_inc(v___x_1766_);
v___x_1768_ = l_Lean_Syntax_matchesNull(v___x_1766_, v___x_1763_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1766_);
lean_dec(v_rhs_1764_);
lean_dec(v_pattern_1721_);
v___x_1769_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1770_, v___x_1768_);
v___x_1772_ = l_Std_Format_defWidth;
v___x_1773_ = l_Std_Format_pretty(v___x_1771_, v___x_1772_, v___x_1720_, v___x_1720_);
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1769_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1775_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v_otherwise_x3f_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1777_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1778_ = l_Lean_Syntax_getArg(v___x_1766_, v___x_1755_);
v___x_1779_ = l_Lean_Syntax_getArg(v___x_1766_, v___x_1777_);
lean_dec(v___x_1766_);
v___x_1780_ = l_Lean_Syntax_isNone(v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
lean_inc(v___x_1779_);
v___x_1781_ = l_Lean_Syntax_matchesNull(v___x_1779_, v___x_1755_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1779_);
lean_dec(v_otherwise_x3f_1778_);
lean_dec(v_rhs_1764_);
lean_dec(v_pattern_1721_);
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1783_, v___x_1781_);
v___x_1785_ = l_Std_Format_defWidth;
v___x_1786_ = l_Std_Format_pretty(v___x_1784_, v___x_1785_, v___x_1720_, v___x_1720_);
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1782_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1788_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1789_;
}
else
{
lean_object* v_body_x3f_x3f_1790_; lean_object* v___x_1791_; 
lean_dec(v_decl_1671_);
v_body_x3f_x3f_1790_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1720_);
lean_dec(v___x_1779_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_body_x3f_x3f_1790_);
v___y_1744_ = v_rhs_1764_;
v___y_1745_ = v_otherwise_x3f_1778_;
v_body_x3f_x3f_1746_ = v___x_1791_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
v___y_1751_ = v___y_1761_;
v___y_1752_ = v___y_1762_;
goto v___jp_1743_;
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1779_);
lean_dec(v_decl_1671_);
v___x_1792_ = lean_box(0);
v___y_1744_ = v_rhs_1764_;
v___y_1745_ = v_otherwise_x3f_1778_;
v_body_x3f_x3f_1746_ = v___x_1792_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
v___y_1751_ = v___y_1761_;
v___y_1752_ = v___y_1762_;
goto v___jp_1743_;
}
}
}
else
{
lean_object* v___x_1793_; 
lean_dec(v___x_1766_);
lean_dec(v_decl_1671_);
v___x_1793_ = lean_box(0);
v___y_1723_ = v_rhs_1764_;
v_otherwise_x3f_1724_ = v___x_1793_;
v_body_x3f_x3f_1725_ = v___x_1793_;
v___y_1726_ = v___y_1757_;
v___y_1727_ = v___y_1758_;
v___y_1728_ = v___y_1759_;
v___y_1729_ = v___y_1760_;
v___y_1730_ = v___y_1761_;
v___y_1731_ = v___y_1762_;
goto v___jp_1722_;
}
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v_x_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v_x_1817_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1816_);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1817_);
v___x_1832_ = l_Lean_Syntax_isOfKind(v_x_1817_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_x_1817_);
v___x_1833_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1834_ = lean_box(0);
v___x_1835_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1834_, v___x_1832_);
v___x_1836_ = l_Std_Format_defWidth;
v___x_1837_ = l_Std_Format_pretty(v___x_1835_, v___x_1836_, v___x_1816_, v___x_1816_);
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1833_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1839_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1841_);
v___x_1843_ = l_Lean_Syntax_isNone(v___x_1842_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1844_; 
lean_inc(v___x_1842_);
v___x_1844_ = l_Lean_Syntax_matchesNull(v___x_1842_, v___x_1841_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v___x_1842_);
lean_dec(v_x_1817_);
v___x_1845_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1846_, v___x_1844_);
v___x_1848_ = l_Std_Format_defWidth;
v___x_1849_ = l_Std_Format_pretty(v___x_1847_, v___x_1848_, v___x_1816_, v___x_1816_);
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1845_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1851_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1842_, v___x_1816_);
lean_dec(v___x_1842_);
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1855_ = l_Lean_Syntax_isOfKind(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v_x_1817_);
v___x_1856_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1857_ = lean_box(0);
v___x_1858_ = l_Lean_Syntax_formatStx(v_decl_1671_, v___x_1857_, v___x_1855_);
v___x_1859_ = l_Std_Format_defWidth;
v___x_1860_ = l_Std_Format_pretty(v___x_1858_, v___x_1859_, v___x_1816_, v___x_1816_);
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1856_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1862_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1863_;
}
else
{
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
v___y_1823_ = v_a_1676_;
v___y_1824_ = v_a_1677_;
goto v___jp_1818_;
}
}
}
else
{
lean_dec(v___x_1842_);
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
v___y_1823_ = v_a_1676_;
v___y_1824_ = v_a_1677_;
goto v___jp_1818_;
}
}
v___jp_1818_:
{
lean_object* v___x_1825_; lean_object* v_rhs_1826_; 
v___x_1825_ = lean_unsigned_to_nat(3u);
v_rhs_1826_ = l_Lean_Syntax_getArg(v_decl_1671_, v___x_1825_);
lean_dec(v_decl_1671_);
if (v_reassignment_1670_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v_x_1817_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1824_;
v___y_1682_ = v___y_1822_;
v___y_1683_ = v___y_1821_;
v___y_1684_ = v_rhs_1826_;
v___y_1685_ = v___y_1823_;
v___y_1686_ = v___y_1819_;
v___y_1687_ = v___x_1827_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_unsigned_to_nat(1u);
v___x_1829_ = lean_mk_empty_array_with_capacity(v___x_1828_);
v___x_1830_ = lean_array_push(v___x_1829_, v_x_1817_);
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1824_;
v___y_1682_ = v___y_1822_;
v___y_1683_ = v___y_1821_;
v___y_1684_ = v_rhs_1826_;
v___y_1685_ = v___y_1823_;
v___y_1686_ = v___y_1819_;
v___y_1687_ = v___x_1830_;
goto v___jp_1679_;
}
}
}
v___jp_1679_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___y_1684_);
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1687_, v___x_1688_, v___x_1689_, v___x_1689_, v___y_1686_, v___y_1680_, v___y_1683_, v___y_1682_, v___y_1685_, v___y_1681_);
return v___x_1690_;
}
v___jp_1691_:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___y_1693_);
if (lean_obj_tag(v___y_1694_) == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1695_, v___x_1702_, v___y_1692_, v___x_1703_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1704_;
}
else
{
lean_object* v_val_1705_; lean_object* v___x_1706_; 
v_val_1705_ = lean_ctor_get(v___y_1694_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___y_1694_, 1);
v___x_1706_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1695_, v___x_1702_, v___y_1692_, v_val_1705_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1980_, size_t v_sz_1981_, size_t v_i_1982_, lean_object* v_b_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_usize_dec_lt(v_i_1982_, v_sz_1981_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_b_1983_);
return v___x_1992_;
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1994_; 
v_a_1993_ = lean_array_uget_borrowed(v_as_1980_, v_i_1982_);
lean_inc(v_a_1993_);
v___x_1994_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1993_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v___x_1996_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1995_, v_b_1983_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1982_, v___x_1997_);
v_i_1982_ = v___x_1998_;
v_b_1983_ = v___x_1996_;
goto _start;
}
else
{
lean_dec_ref(v_b_1983_);
return v___x_1994_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2014_ = l_Lean_stringToMessageData(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2029_, lean_object* v_as_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_a_2042_; uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_b_2033_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v_a_2049_; uint8_t v___x_2050_; 
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2049_ = lean_array_uget_borrowed(v_as_2030_, v_i_2032_);
lean_inc(v_a_2049_);
v___x_2050_ = l_Lean_Syntax_isOfKind(v_a_2049_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref_known(v___x_2051_, 1);
v_a_2042_ = v_b_2033_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_b_2033_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___y_2063_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_unsigned_to_nat(3u);
v___x_2080_ = l_Lean_Syntax_getArg(v_a_2049_, v___x_2060_);
v___x_2081_ = l_Lean_Syntax_getArgs(v___x_2080_);
lean_dec(v___x_2080_);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2084_ = lean_array_get_size(v___x_2081_);
v___x_2085_ = lean_nat_dec_lt(v___x_2082_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v___x_2081_);
v___y_2063_ = v___x_2083_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2086_ = lean_box(v___x_2050_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2083_);
v___x_2088_ = lean_nat_dec_le(v___x_2084_, v___x_2084_);
if (v___x_2088_ == 0)
{
if (v___x_2085_ == 0)
{
lean_dec_ref_known(v___x_2087_, 2);
lean_dec_ref(v___x_2081_);
v___y_2063_ = v___x_2083_;
goto v___jp_2062_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v_snd_2092_; 
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = lean_usize_of_nat(v___x_2084_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2050_, v___x_2029_, v___x_2081_, v___x_2089_, v___x_2090_, v___x_2087_);
lean_dec_ref(v___x_2081_);
v_snd_2092_ = lean_ctor_get(v___x_2091_, 1);
lean_inc(v_snd_2092_);
lean_dec_ref(v___x_2091_);
v___y_2063_ = v_snd_2092_;
goto v___jp_2062_;
}
}
else
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v_snd_2096_; 
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = lean_usize_of_nat(v___x_2084_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2050_, v___x_2029_, v___x_2081_, v___x_2093_, v___x_2094_, v___x_2087_);
lean_dec_ref(v___x_2081_);
v_snd_2096_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_snd_2096_);
lean_dec_ref(v___x_2095_);
v___y_2063_ = v_snd_2096_;
goto v___jp_2062_;
}
}
v___jp_2062_:
{
size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v_sz_2064_ = lean_array_size(v___y_2063_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2064_, v___x_2065_, v___y_2063_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_dec_ref_known(v___x_2067_, 1);
v_a_2042_ = v_b_2033_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_b_2033_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref_known(v___x_2066_, 1);
v___x_2076_ = l_Lean_Syntax_getArg(v_a_2049_, v___x_2061_);
v___x_2077_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2076_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2033_, v_a_2078_);
v_a_2042_ = v___x_2079_;
goto v___jp_2041_;
}
else
{
lean_dec_ref(v_b_2033_);
return v___x_2077_;
}
}
}
}
}
v___jp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2032_, v___x_2043_);
v_i_2032_ = v___x_2044_;
v_b_2033_ = v_a_2042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2097_, size_t v_sz_2098_, size_t v_i_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_a_2109_; uint8_t v___x_2113_; 
v___x_2113_ = lean_usize_dec_lt(v_i_2099_, v_sz_2098_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_b_2100_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v_a_2116_ = lean_array_uget_borrowed(v_as_2097_, v_i_2099_);
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2116_);
v___x_2130_ = l_Lean_Syntax_isOfKind(v_a_2116_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2116_);
v___x_2132_ = l_Lean_Syntax_isOfKind(v_a_2116_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2134_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2135_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2134_, v___x_2132_);
v___x_2136_ = l_Std_Format_defWidth;
v___x_2137_ = l_Std_Format_pretty(v___x_2135_, v___x_2136_, v___x_2115_, v___x_2115_);
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2133_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2139_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref_known(v___x_2140_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_b_2100_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2150_);
v___x_2152_ = l_Lean_Syntax_isOfKind(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v___x_2150_);
v___x_2153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2154_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2155_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2154_, v___x_2152_);
v___x_2156_ = l_Std_Format_defWidth;
v___x_2157_ = l_Std_Format_pretty(v___x_2155_, v___x_2156_, v___x_2115_, v___x_2115_);
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2153_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2159_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_dec_ref_known(v___x_2160_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v_b_2100_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2169_ = l_Lean_Syntax_getArg(v___x_2150_, v___x_2115_);
lean_dec(v___x_2150_);
v___x_2170_ = l_Lean_Syntax_getArgs(v___x_2169_);
lean_dec(v___x_2169_);
v_sz_2171_ = lean_array_size(v___x_2170_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2130_, v___x_2170_, v_sz_2171_, v___x_2172_, v_b_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec_ref(v___x_2170_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v_a_2109_ = v_a_2174_;
goto v___jp_2108_;
}
else
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_unsigned_to_nat(2u);
v___x_2176_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2175_);
v___x_2177_ = l_Lean_Syntax_isNone(v___x_2176_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_Syntax_matchesNull(v___x_2176_, v___x_2175_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2179_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2180_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2181_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2180_, v___x_2178_);
v___x_2182_ = l_Std_Format_defWidth;
v___x_2183_ = l_Std_Format_pretty(v___x_2181_, v___x_2182_, v___x_2115_, v___x_2115_);
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2179_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2185_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref_known(v___x_2186_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_b_2100_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
v___y_2118_ = v___y_2101_;
v___y_2119_ = v___y_2102_;
v___y_2120_ = v___y_2103_;
v___y_2121_ = v___y_2104_;
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
goto v___jp_2117_;
}
}
else
{
lean_dec(v___x_2176_);
v___y_2118_ = v___y_2101_;
v___y_2119_ = v___y_2102_;
v___y_2120_ = v___y_2103_;
v___y_2121_ = v___y_2104_;
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
goto v___jp_2117_;
}
}
v___jp_2117_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(4u);
v___x_2125_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2124_);
v___x_2126_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2125_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2127_, v_b_2100_);
v_a_2109_ = v___x_2128_;
goto v___jp_2108_;
}
else
{
lean_dec_ref(v_b_2100_);
return v___x_2126_;
}
}
}
v___jp_2108_:
{
size_t v___x_2110_; size_t v___x_2111_; 
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_add(v_i_2099_, v___x_2110_);
v_i_2099_ = v___x_2111_;
v_b_2100_ = v_a_2109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2195_) == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2206_; 
v_val_2205_ = lean_ctor_get(v_stx_x3f_2195_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v_stx_x3f_2195_, 1);
v___x_2206_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2205_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2213_, lean_object* v_as_2214_, size_t v_sz_2215_, size_t v_i_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_a_2226_; uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_lt(v_i_2216_, v_sz_2215_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_b_2217_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v_a_2233_; uint8_t v___x_2234_; 
v___x_2232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2233_ = lean_array_uget_borrowed(v_as_2214_, v_i_2216_);
lean_inc(v_a_2233_);
v___x_2234_ = l_Lean_Syntax_isOfKind(v_a_2233_, v___x_2232_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec_ref_known(v___x_2235_, 1);
v_a_2226_ = v_b_2217_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v_b_2217_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___y_2247_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_unsigned_to_nat(3u);
v___x_2264_ = l_Lean_Syntax_getArg(v_a_2233_, v___x_2244_);
v___x_2265_ = l_Lean_Syntax_getArgs(v___x_2264_);
lean_dec(v___x_2264_);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2268_ = lean_array_get_size(v___x_2265_);
v___x_2269_ = lean_nat_dec_lt(v___x_2266_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v___x_2265_);
v___y_2247_ = v___x_2267_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = lean_box(v___x_2234_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2267_);
v___x_2272_ = lean_nat_dec_le(v___x_2268_, v___x_2268_);
if (v___x_2272_ == 0)
{
if (v___x_2269_ == 0)
{
lean_dec_ref_known(v___x_2271_, 2);
lean_dec_ref(v___x_2265_);
v___y_2247_ = v___x_2267_;
goto v___jp_2246_;
}
else
{
size_t v___x_2273_; size_t v___x_2274_; lean_object* v___x_2275_; lean_object* v_snd_2276_; 
v___x_2273_ = ((size_t)0ULL);
v___x_2274_ = lean_usize_of_nat(v___x_2268_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2234_, v___x_2213_, v___x_2265_, v___x_2273_, v___x_2274_, v___x_2271_);
lean_dec_ref(v___x_2265_);
v_snd_2276_ = lean_ctor_get(v___x_2275_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v___x_2275_);
v___y_2247_ = v_snd_2276_;
goto v___jp_2246_;
}
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; lean_object* v_snd_2280_; 
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2268_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2234_, v___x_2213_, v___x_2265_, v___x_2277_, v___x_2278_, v___x_2271_);
lean_dec_ref(v___x_2265_);
v_snd_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2279_);
v___y_2247_ = v_snd_2280_;
goto v___jp_2246_;
}
}
v___jp_2246_:
{
size_t v_sz_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v_sz_2248_ = lean_array_size(v___y_2247_);
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2248_, v___x_2249_, v___y_2247_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_dec_ref_known(v___x_2251_, 1);
v_a_2226_ = v_b_2217_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v_b_2217_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref_known(v___x_2250_, 1);
v___x_2260_ = l_Lean_Syntax_getArg(v_a_2233_, v___x_2245_);
v___x_2261_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2260_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2217_, v_a_2262_);
v_a_2226_ = v___x_2263_;
goto v___jp_2225_;
}
else
{
lean_dec_ref(v_b_2217_);
return v___x_2261_;
}
}
}
}
}
v___jp_2225_:
{
size_t v___x_2227_; size_t v___x_2228_; 
v___x_2227_ = ((size_t)1ULL);
v___x_2228_ = lean_usize_add(v_i_2216_, v___x_2227_);
v_i_2216_ = v___x_2228_;
v_b_2217_ = v_a_2226_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2317_ = l_Lean_NameSet_empty;
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = 0;
v___x_2320_ = 1;
v___x_2321_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2321_, 0, v___x_2318_);
lean_ctor_set(v___x_2321_, 1, v___x_2317_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2, v___x_2320_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2 + 1, v___x_2319_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2 + 2, v___x_2319_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2 + 3, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2344_; lean_object* v_bodyInfo_2345_; lean_object* v___y_2349_; lean_object* v_bodyInfo_2350_; lean_object* v___x_2353_; lean_object* v_env_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = lean_st_ref_get(v_a_2328_);
v_env_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_env_2354_);
lean_dec(v___x_2353_);
lean_inc(v_stx_2322_);
v___x_2355_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2355_, 0, v_env_2354_);
lean_closure_set(v___x_2355_, 1, v_stx_2322_);
v___x_2356_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2355_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_4441_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_4441_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_4441_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
if (lean_obj_tag(v_a_2357_) == 1)
{
lean_object* v_val_2361_; lean_object* v_snd_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_del_object(v___x_2359_);
lean_dec(v_stx_2322_);
v_val_2361_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v_a_2357_, 1);
v_snd_2362_ = lean_ctor_get(v_val_2361_, 1);
lean_inc(v_snd_2362_);
lean_dec(v_val_2361_);
v___x_2363_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2363_, 0, lean_box(0));
lean_closure_set(v___x_2363_, 1, v_snd_2362_);
v___x_2364_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2363_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_stx_2322_ = v_a_2365_;
goto _start;
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2364_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2364_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___x_2557_; uint8_t v___x_2558_; uint8_t v___x_2559_; 
lean_dec(v_a_2357_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2322_);
v___x_2558_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2557_);
v___x_2559_ = 1;
if (v___x_2558_ == 0)
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2322_);
v___x_2561_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2322_);
v___x_2563_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2322_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2322_);
v___x_2567_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2322_);
v___x_2569_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
lean_del_object(v___x_2359_);
v___x_2570_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2322_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2322_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; uint8_t v___x_2575_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; 
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2322_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2322_);
v___x_2637_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2322_);
v___x_2639_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2322_);
v___x_2641_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2322_);
v___x_2643_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2322_);
v___x_2645_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2322_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2322_);
v___x_2649_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2322_);
v___x_2651_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2322_);
v___x_2653_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50));
lean_inc(v_stx_2322_);
v___x_2655_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2322_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2322_);
v___x_2659_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2322_);
v___x_2661_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2322_);
v___x_2663_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2322_);
v___x_2665_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2322_);
v___x_2667_ = l_Lean_Syntax_isOfKind(v_stx_2322_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v_env_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2668_ = lean_st_ref_get(v_a_2328_);
v_env_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_env_2669_);
lean_dec(v___x_2668_);
lean_inc_n(v_stx_2322_, 2);
v___x_2670_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2671_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2672_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2671_, v_env_2669_, v___x_2670_);
v___x_2673_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2674_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2672_, v___x_2673_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_2672_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2705_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2705_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2705_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_fst_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2703_; 
v_fst_2679_ = lean_ctor_get(v_a_2675_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2675_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; 
v_unused_2704_ = lean_ctor_get(v_a_2675_, 1);
lean_dec(v_unused_2704_);
v___x_2681_ = v_a_2675_;
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_fst_2679_);
lean_dec(v_a_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2703_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
if (lean_obj_tag(v_fst_2679_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_del_object(v___x_2677_);
v___x_2683_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2684_ = l_Lean_MessageData_ofName(v___x_2670_);
lean_inc_ref(v___x_2684_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 7);
lean_ctor_set(v___x_2681_, 1, v___x_2684_);
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2686_ = v___x_2681_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2687_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2690_ = l_Lean_indentD(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2684_);
v___x_2695_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2696_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2697_;
}
}
else
{
lean_object* v_val_2699_; lean_object* v___x_2701_; 
lean_del_object(v___x_2681_);
lean_dec(v___x_2670_);
lean_dec(v_stx_2322_);
v_val_2699_ = lean_ctor_get(v_fst_2679_, 0);
lean_inc(v_val_2699_);
lean_dec_ref_known(v_fst_2679_, 1);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v_val_2699_);
v___x_2701_ = v___x_2677_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_val_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v___x_2670_);
lean_dec(v_stx_2322_);
v_a_2706_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2674_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2674_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___y_2718_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_unsigned_to_nat(5u);
v___x_2716_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2715_);
v___x_2727_ = lean_unsigned_to_nat(6u);
v___x_2728_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2727_);
lean_dec(v_stx_2322_);
v___x_2729_ = l_Lean_Syntax_getOptional_x3f(v___x_2728_);
lean_dec(v___x_2728_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_box(0);
v___y_2718_ = v___x_2730_;
goto v___jp_2717_;
}
else
{
lean_object* v_val_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_val_2731_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_val_2731_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_val_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
v___y_2718_ = v___x_2736_;
goto v___jp_2717_;
}
}
}
v___jp_2717_:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2716_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2719_) == 0)
{
if (lean_obj_tag(v___y_2718_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = l_Lean_NameSet_empty;
v___x_2722_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2714_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2, v___x_2665_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2 + 1, v___x_2665_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2 + 2, v___x_2665_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2 + 3, v___x_2665_);
v___y_2349_ = v_a_2720_;
v_bodyInfo_2350_ = v___x_2722_;
goto v___jp_2348_;
}
else
{
lean_object* v_a_2723_; lean_object* v_val_2724_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2719_, 1);
v_val_2724_ = lean_ctor_get(v___y_2718_, 0);
lean_inc(v_val_2724_);
lean_dec_ref_known(v___y_2718_, 1);
v___x_2725_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2724_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2349_ = v_a_2723_;
v_bodyInfo_2350_ = v_a_2726_;
goto v___jp_2348_;
}
else
{
lean_dec(v_a_2723_);
return v___x_2725_;
}
}
}
else
{
lean_dec(v___y_2718_);
return v___x_2719_;
}
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___y_2743_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_unsigned_to_nat(5u);
v___x_2741_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2740_);
v___x_2752_ = lean_unsigned_to_nat(6u);
v___x_2753_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2752_);
lean_dec(v_stx_2322_);
v___x_2754_ = l_Lean_Syntax_getOptional_x3f(v___x_2753_);
lean_dec(v___x_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_box(0);
v___y_2743_ = v___x_2755_;
goto v___jp_2742_;
}
else
{
lean_object* v_val_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_val_2756_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_val_2756_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_val_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
v___y_2743_ = v___x_2761_;
goto v___jp_2742_;
}
}
}
v___jp_2742_:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2741_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2744_) == 0)
{
if (lean_obj_tag(v___y_2743_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l_Lean_NameSet_empty;
v___x_2747_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2747_, 0, v___x_2739_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*2, v___x_2663_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*2 + 1, v___x_2663_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*2 + 2, v___x_2663_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*2 + 3, v___x_2663_);
v___y_2344_ = v_a_2745_;
v_bodyInfo_2345_ = v___x_2747_;
goto v___jp_2343_;
}
else
{
lean_object* v_a_2748_; lean_object* v_val_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2744_, 1);
v_val_2749_ = lean_ctor_get(v___y_2743_, 0);
lean_inc(v_val_2749_);
lean_dec_ref_known(v___y_2743_, 1);
v___x_2750_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2749_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___y_2344_ = v_a_2748_;
v_bodyInfo_2345_ = v_a_2751_;
goto v___jp_2343_;
}
else
{
lean_dec(v_a_2748_);
return v___x_2750_;
}
}
}
else
{
lean_dec(v___y_2743_);
return v___x_2744_;
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2979_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2765_);
v___x_2980_ = l_Lean_Syntax_isNone(v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = lean_unsigned_to_nat(5u);
v___x_2982_ = l_Lean_Syntax_matchesNull(v___x_2979_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2983_ = lean_st_ref_get(v_a_2328_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_env_2984_);
lean_dec(v___x_2983_);
lean_inc_n(v_stx_2322_, 2);
v___x_2985_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2986_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2987_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2986_, v_env_2984_, v___x_2985_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2989_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2987_, v___x_2988_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
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
v___x_2998_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2999_ = l_Lean_MessageData_ofName(v___x_2985_);
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
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3005_ = l_Lean_indentD(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3003_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___x_2999_);
v___x_3010_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3011_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3012_;
}
}
else
{
lean_object* v_val_3014_; lean_object* v___x_3016_; 
lean_del_object(v___x_2996_);
lean_dec(v___x_2985_);
lean_dec(v_stx_2322_);
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
lean_dec(v___x_2985_);
lean_dec(v_stx_2322_);
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
v___y_2767_ = v_a_2323_;
v___y_2768_ = v_a_2324_;
v___y_2769_ = v_a_2325_;
v___y_2770_ = v_a_2326_;
v___y_2771_ = v_a_2327_;
v___y_2772_ = v_a_2328_;
goto v___jp_2766_;
}
}
else
{
lean_dec(v___x_2979_);
v___y_2767_ = v_a_2323_;
v___y_2768_ = v_a_2324_;
v___y_2769_ = v_a_2325_;
v___y_2770_ = v_a_2326_;
v___y_2771_ = v_a_2327_;
v___y_2772_ = v_a_2328_;
goto v___jp_2766_;
}
v___jp_2766_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2773_ = lean_unsigned_to_nat(4u);
v___x_2774_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2773_);
v___x_2775_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v___x_2774_);
v___x_2776_ = l_Lean_Syntax_isOfKind(v___x_2774_, v___x_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v_env_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v___x_2774_);
v___x_2777_ = lean_st_ref_get(v___y_2772_);
v_env_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_env_2778_);
lean_dec(v___x_2777_);
lean_inc_n(v_stx_2322_, 2);
v___x_2779_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2780_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2781_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2780_, v_env_2778_, v___x_2779_);
v___x_2782_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2783_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2781_, v___x_2782_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___x_2781_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2814_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2814_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2814_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v_fst_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2812_; 
v_fst_2788_ = lean_ctor_get(v_a_2784_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_a_2784_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v_a_2784_, 1);
lean_dec(v_unused_2813_);
v___x_2790_ = v_a_2784_;
v_isShared_2791_ = v_isSharedCheck_2812_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_fst_2788_);
lean_dec(v_a_2784_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2812_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
if (lean_obj_tag(v_fst_2788_) == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_del_object(v___x_2786_);
v___x_2792_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2793_ = l_Lean_MessageData_ofName(v___x_2779_);
lean_inc_ref(v___x_2793_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 7);
lean_ctor_set(v___x_2790_, 1, v___x_2793_);
lean_ctor_set(v___x_2790_, 0, v___x_2792_);
v___x_2795_ = v___x_2790_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2796_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2799_ = l_Lean_indentD(v___x_2798_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2797_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2793_);
v___x_2804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2805_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2806_;
}
}
else
{
lean_object* v_val_2808_; lean_object* v___x_2810_; 
lean_del_object(v___x_2790_);
lean_dec(v___x_2779_);
lean_dec(v_stx_2322_);
v_val_2808_ = lean_ctor_get(v_fst_2788_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_fst_2788_, 1);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v_val_2808_);
v___x_2810_ = v___x_2786_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_val_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v___x_2779_);
lean_dec(v_stx_2322_);
v_a_2815_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2783_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2783_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2823_ = l_Lean_Syntax_getArg(v___x_2774_, v___x_2764_);
v___x_2824_ = l_Lean_Syntax_getArgs(v___x_2823_);
lean_dec(v___x_2823_);
v_sz_2825_ = lean_array_size(v___x_2824_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2825_, v___x_2826_, v___x_2824_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2828_; lean_object* v_env_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec(v___x_2774_);
v___x_2828_ = lean_st_ref_get(v___y_2772_);
v_env_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2829_);
lean_dec(v___x_2828_);
lean_inc_n(v_stx_2322_, 2);
v___x_2830_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2831_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2832_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2831_, v_env_2829_, v___x_2830_);
v___x_2833_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2834_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2832_, v___x_2833_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___x_2832_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2865_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2865_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2865_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v_fst_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2863_; 
v_fst_2839_ = lean_ctor_get(v_a_2835_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_a_2835_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v_a_2835_, 1);
lean_dec(v_unused_2864_);
v___x_2841_ = v_a_2835_;
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_fst_2839_);
lean_dec(v_a_2835_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
if (lean_obj_tag(v_fst_2839_) == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
lean_del_object(v___x_2837_);
v___x_2843_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2844_ = l_Lean_MessageData_ofName(v___x_2830_);
lean_inc_ref(v___x_2844_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 7);
lean_ctor_set(v___x_2841_, 1, v___x_2844_);
lean_ctor_set(v___x_2841_, 0, v___x_2843_);
v___x_2846_ = v___x_2841_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2847_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2850_ = l_Lean_indentD(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2848_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2844_);
v___x_2855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2856_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2857_;
}
}
else
{
lean_object* v_val_2859_; lean_object* v___x_2861_; 
lean_del_object(v___x_2841_);
lean_dec(v___x_2830_);
lean_dec(v_stx_2322_);
v_val_2859_ = lean_ctor_get(v_fst_2839_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v_fst_2839_, 1);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v_val_2859_);
v___x_2861_ = v___x_2837_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_val_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v___x_2830_);
lean_dec(v_stx_2322_);
v_a_2866_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2834_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2834_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_val_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_val_2874_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2875_ = l_Lean_Syntax_getArg(v___x_2774_, v___x_2765_);
lean_dec(v___x_2774_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v___x_2875_);
v___x_2877_ = l_Lean_Syntax_isOfKind(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v_env_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v___x_2875_);
lean_dec(v_val_2874_);
v___x_2878_ = lean_st_ref_get(v___y_2772_);
v_env_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc_ref(v_env_2879_);
lean_dec(v___x_2878_);
lean_inc_n(v_stx_2322_, 2);
v___x_2880_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2881_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2882_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2881_, v_env_2879_, v___x_2880_);
v___x_2883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2884_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2882_, v___x_2883_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2915_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_fst_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2913_; 
v_fst_2889_ = lean_ctor_get(v_a_2885_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_a_2885_, 1);
lean_dec(v_unused_2914_);
v___x_2891_ = v_a_2885_;
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_fst_2889_);
lean_dec(v_a_2885_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
if (lean_obj_tag(v_fst_2889_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_del_object(v___x_2887_);
v___x_2893_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2894_ = l_Lean_MessageData_ofName(v___x_2880_);
lean_inc_ref(v___x_2894_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 7);
lean_ctor_set(v___x_2891_, 1, v___x_2894_);
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2896_ = v___x_2891_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2897_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2900_ = l_Lean_indentD(v___x_2899_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2898_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v___x_2894_);
v___x_2905_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2906_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2907_;
}
}
else
{
lean_object* v_val_2909_; lean_object* v___x_2911_; 
lean_del_object(v___x_2891_);
lean_dec(v___x_2880_);
lean_dec(v_stx_2322_);
v_val_2909_ = lean_ctor_get(v_fst_2889_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v_fst_2889_, 1);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_val_2909_);
v___x_2911_ = v___x_2887_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_val_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v___x_2880_);
lean_dec(v_stx_2322_);
v_a_2916_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2884_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2884_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = l_Lean_Syntax_getArg(v___x_2875_, v___x_2765_);
v___x_2925_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
v___x_2926_ = l_Lean_Syntax_isOfKind(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v_env_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v___x_2875_);
lean_dec(v_val_2874_);
v___x_2927_ = lean_st_ref_get(v___y_2772_);
v_env_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc_ref(v_env_2928_);
lean_dec(v___x_2927_);
lean_inc_n(v_stx_2322_, 2);
v___x_2929_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2930_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2931_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2930_, v_env_2928_, v___x_2929_);
v___x_2932_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2933_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2931_, v___x_2932_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___x_2931_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2964_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2964_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2964_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_fst_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2962_; 
v_fst_2938_ = lean_ctor_get(v_a_2934_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_a_2934_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_a_2934_, 1);
lean_dec(v_unused_2963_);
v___x_2940_ = v_a_2934_;
v_isShared_2941_ = v_isSharedCheck_2962_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_fst_2938_);
lean_dec(v_a_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2962_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
if (lean_obj_tag(v_fst_2938_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_del_object(v___x_2936_);
v___x_2942_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2943_ = l_Lean_MessageData_ofName(v___x_2929_);
lean_inc_ref(v___x_2943_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set_tag(v___x_2940_, 7);
lean_ctor_set(v___x_2940_, 1, v___x_2943_);
lean_ctor_set(v___x_2940_, 0, v___x_2942_);
v___x_2945_ = v___x_2940_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2946_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2949_ = l_Lean_indentD(v___x_2948_);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2947_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2943_);
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2955_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2956_;
}
}
else
{
lean_object* v_val_2958_; lean_object* v___x_2960_; 
lean_del_object(v___x_2940_);
lean_dec(v___x_2929_);
lean_dec(v_stx_2322_);
v_val_2958_ = lean_ctor_get(v_fst_2938_, 0);
lean_inc(v_val_2958_);
lean_dec_ref_known(v_fst_2938_, 1);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_val_2958_);
v___x_2960_ = v___x_2936_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_val_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___x_2929_);
lean_dec(v_stx_2322_);
v_a_2965_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2933_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2933_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v_stx_2322_);
v___x_2973_ = lean_unsigned_to_nat(3u);
v___x_2974_ = l_Lean_Syntax_getArg(v___x_2875_, v___x_2973_);
lean_dec(v___x_2875_);
v___x_2975_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2974_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; size_t v_sz_2977_; lean_object* v___x_2978_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v_sz_2977_ = lean_array_size(v_val_2874_);
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2874_, v_sz_2977_, v___x_2826_, v_a_2976_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v_val_2874_);
return v___x_2978_;
}
else
{
lean_dec(v_val_2874_);
return v___x_2975_;
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
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v_stx_2322_);
v___x_3029_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_dec(v_stx_2322_);
v___x_3031_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
return v___x_3032_;
}
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec(v_stx_2322_);
v___x_3033_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
else
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec(v_stx_2322_);
v___x_3035_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3037_ = lean_unsigned_to_nat(2u);
v___x_3038_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3037_);
v___x_3039_ = l_Lean_Syntax_getArgs(v___x_3038_);
lean_dec(v___x_3038_);
v_sz_3040_ = lean_array_size(v___x_3039_);
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3040_, v___x_3041_, v___x_3039_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v___x_3043_; lean_object* v_env_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3043_ = lean_st_ref_get(v_a_2328_);
v_env_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc_ref(v_env_3044_);
lean_dec(v___x_3043_);
lean_inc_n(v_stx_2322_, 2);
v___x_3045_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3046_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3047_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3046_, v_env_3044_, v___x_3045_);
v___x_3048_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3049_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3047_, v___x_3048_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3047_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3080_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3080_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3080_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_fst_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3078_; 
v_fst_3054_ = lean_ctor_get(v_a_3050_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_a_3050_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v_a_3050_, 1);
lean_dec(v_unused_3079_);
v___x_3056_ = v_a_3050_;
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_fst_3054_);
lean_dec(v_a_3050_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
if (lean_obj_tag(v_fst_3054_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_del_object(v___x_3052_);
v___x_3058_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3059_ = l_Lean_MessageData_ofName(v___x_3045_);
lean_inc_ref(v___x_3059_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 7);
lean_ctor_set(v___x_3056_, 1, v___x_3059_);
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3061_ = v___x_3056_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3062_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3065_ = l_Lean_indentD(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3063_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3059_);
v___x_3070_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3071_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3072_;
}
}
else
{
lean_object* v_val_3074_; lean_object* v___x_3076_; 
lean_del_object(v___x_3056_);
lean_dec(v___x_3045_);
lean_dec(v_stx_2322_);
v_val_3074_ = lean_ctor_get(v_fst_3054_, 0);
lean_inc(v_val_3074_);
lean_dec_ref_known(v_fst_3054_, 1);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v_val_3074_);
v___x_3076_ = v___x_3052_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_val_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v___x_3045_);
lean_dec(v_stx_2322_);
v_a_3081_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3049_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3049_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v_val_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3223_; 
v_val_3089_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3091_ = v___x_3042_;
v_isShared_3092_ = v_isSharedCheck_3223_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_val_3089_);
lean_dec(v___x_3042_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3223_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_finSeq_x3f_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3093_ = lean_unsigned_to_nat(1u);
v___x_3094_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3093_);
v___x_3118_ = lean_unsigned_to_nat(3u);
v___x_3119_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3118_);
v___x_3120_ = l_Lean_Syntax_isNone(v___x_3119_);
if (v___x_3120_ == 0)
{
uint8_t v___x_3121_; 
lean_inc(v___x_3119_);
v___x_3121_ = l_Lean_Syntax_matchesNull(v___x_3119_, v___x_3093_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v_env_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v___x_3119_);
lean_dec(v___x_3094_);
lean_del_object(v___x_3091_);
lean_dec(v_val_3089_);
v___x_3122_ = lean_st_ref_get(v_a_2328_);
v_env_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_env_3123_);
lean_dec(v___x_3122_);
lean_inc_n(v_stx_2322_, 2);
v___x_3124_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3125_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3126_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3125_, v_env_3123_, v___x_3124_);
v___x_3127_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3128_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3126_, v___x_3127_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3126_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3159_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3159_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3159_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v_fst_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3157_; 
v_fst_3133_ = lean_ctor_get(v_a_3129_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_a_3129_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v_a_3129_, 1);
lean_dec(v_unused_3158_);
v___x_3135_ = v_a_3129_;
v_isShared_3136_ = v_isSharedCheck_3157_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_fst_3133_);
lean_dec(v_a_3129_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3157_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
if (lean_obj_tag(v_fst_3133_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_del_object(v___x_3131_);
v___x_3137_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3138_ = l_Lean_MessageData_ofName(v___x_3124_);
lean_inc_ref(v___x_3138_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 7);
lean_ctor_set(v___x_3135_, 1, v___x_3138_);
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3140_ = v___x_3135_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3141_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3144_ = l_Lean_indentD(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3142_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3138_);
v___x_3149_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3150_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3151_;
}
}
else
{
lean_object* v_val_3153_; lean_object* v___x_3155_; 
lean_del_object(v___x_3135_);
lean_dec(v___x_3124_);
lean_dec(v_stx_2322_);
v_val_3153_ = lean_ctor_get(v_fst_3133_, 0);
lean_inc(v_val_3153_);
lean_dec_ref_known(v_fst_3133_, 1);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_val_3153_);
v___x_3155_ = v___x_3131_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_val_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___x_3124_);
lean_dec(v_stx_2322_);
v_a_3160_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3128_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3128_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l_Lean_Syntax_getArg(v___x_3119_, v___x_3168_);
lean_dec(v___x_3119_);
v___x_3170_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_3169_);
v___x_3171_ = l_Lean_Syntax_isOfKind(v___x_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v_env_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec(v___x_3169_);
lean_dec(v___x_3094_);
lean_del_object(v___x_3091_);
lean_dec(v_val_3089_);
v___x_3172_ = lean_st_ref_get(v_a_2328_);
v_env_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc_ref(v_env_3173_);
lean_dec(v___x_3172_);
lean_inc_n(v_stx_2322_, 2);
v___x_3174_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3175_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3176_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3175_, v_env_3173_, v___x_3174_);
v___x_3177_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3178_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3176_, v___x_3177_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3176_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3209_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3209_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3209_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_fst_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3207_; 
v_fst_3183_ = lean_ctor_get(v_a_3179_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3179_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_a_3179_, 1);
lean_dec(v_unused_3208_);
v___x_3185_ = v_a_3179_;
v_isShared_3186_ = v_isSharedCheck_3207_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_fst_3183_);
lean_dec(v_a_3179_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3207_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
if (lean_obj_tag(v_fst_3183_) == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
lean_del_object(v___x_3181_);
v___x_3187_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3188_ = l_Lean_MessageData_ofName(v___x_3174_);
lean_inc_ref(v___x_3188_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 7);
lean_ctor_set(v___x_3185_, 1, v___x_3188_);
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3190_ = v___x_3185_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3191_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3194_ = l_Lean_indentD(v___x_3193_);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3192_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___x_3188_);
v___x_3199_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3200_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3201_;
}
}
else
{
lean_object* v_val_3203_; lean_object* v___x_3205_; 
lean_del_object(v___x_3185_);
lean_dec(v___x_3174_);
lean_dec(v_stx_2322_);
v_val_3203_ = lean_ctor_get(v_fst_3183_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v_fst_3183_, 1);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_val_3203_);
v___x_3205_ = v___x_3181_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_val_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v___x_3174_);
lean_dec(v_stx_2322_);
v_a_3210_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3178_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3178_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_dec(v_stx_2322_);
v___x_3218_ = l_Lean_Syntax_getArg(v___x_3169_, v___x_3093_);
lean_dec(v___x_3169_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3218_);
v___x_3220_ = v___x_3091_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
v_finSeq_x3f_3096_ = v___x_3220_;
v___y_3097_ = v_a_2323_;
v___y_3098_ = v_a_2324_;
v___y_3099_ = v_a_2325_;
v___y_3100_ = v_a_2326_;
v___y_3101_ = v_a_2327_;
v___y_3102_ = v_a_2328_;
goto v___jp_3095_;
}
}
}
}
else
{
lean_object* v___x_3222_; 
lean_dec(v___x_3119_);
lean_del_object(v___x_3091_);
lean_dec(v_stx_2322_);
v___x_3222_ = lean_box(0);
v_finSeq_x3f_3096_ = v___x_3222_;
v___y_3097_ = v_a_2323_;
v___y_3098_ = v_a_2324_;
v___y_3099_ = v_a_2325_;
v___y_3100_ = v_a_2326_;
v___y_3101_ = v_a_2327_;
v___y_3102_ = v_a_2328_;
goto v___jp_3095_;
}
v___jp_3095_:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3094_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; size_t v_sz_3105_; lean_object* v___x_3106_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v_sz_3105_ = lean_array_size(v_val_3089_);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3089_, v_sz_3105_, v___x_3041_, v_a_3104_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v_val_3089_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3117_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3117_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3117_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3107_, v_a_3109_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3113_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_dec(v_a_3107_);
return v___x_3108_;
}
}
else
{
lean_dec(v_finSeq_x3f_3096_);
return v___x_3106_;
}
}
else
{
lean_dec(v_finSeq_x3f_3096_);
lean_dec(v_val_3089_);
return v___x_3103_;
}
}
}
}
}
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3224_);
lean_dec(v_stx_2322_);
v___x_3226_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3225_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3249_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3249_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3249_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint8_t v_breaks_3231_; uint8_t v_returnsEarly_3232_; lean_object* v_reassigns_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3247_; 
v_breaks_3231_ = lean_ctor_get_uint8(v_a_3227_, sizeof(void*)*2);
v_returnsEarly_3232_ = lean_ctor_get_uint8(v_a_3227_, sizeof(void*)*2 + 2);
v_reassigns_3233_ = lean_ctor_get(v_a_3227_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_a_3227_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v_a_3227_, 0);
lean_dec(v_unused_3248_);
v___x_3235_ = v_a_3227_;
v_isShared_3236_ = v_isSharedCheck_3247_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_reassigns_3233_);
lean_dec(v_a_3227_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3247_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___y_3238_; 
if (v_breaks_3231_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_unsigned_to_nat(0u);
v___y_3238_ = v___x_3246_;
goto v___jp_3237_;
}
else
{
v___y_3238_ = v___x_3224_;
goto v___jp_3237_;
}
v___jp_3237_:
{
uint8_t v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = lean_bool_not(v_breaks_3231_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___y_3238_);
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___y_3238_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_reassigns_3233_);
lean_ctor_set_uint8(v_reuseFailAlloc_3245_, sizeof(void*)*2 + 2, v_returnsEarly_3232_);
v___x_3241_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*2, v___x_2649_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*2 + 1, v___x_2649_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*2 + 3, v___x_3239_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3241_);
v___x_3243_ = v___x_3229_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
else
{
return v___x_3226_;
}
}
}
else
{
lean_object* v___x_3250_; lean_object* v___y_3252_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3323_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3250_);
v___x_3324_ = l_Lean_Syntax_getArgs(v___x_3323_);
lean_dec(v___x_3323_);
v___x_3325_ = lean_unsigned_to_nat(0u);
v___x_3326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3327_ = lean_array_get_size(v___x_3324_);
v___x_3328_ = lean_nat_dec_lt(v___x_3325_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_dec_ref(v___x_3324_);
v___y_3252_ = v___x_3326_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3329_ = lean_box(v___x_2649_);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3326_);
v___x_3331_ = lean_nat_dec_le(v___x_3327_, v___x_3327_);
if (v___x_3331_ == 0)
{
if (v___x_3328_ == 0)
{
lean_dec_ref_known(v___x_3330_, 2);
lean_dec_ref(v___x_3324_);
v___y_3252_ = v___x_3326_;
goto v___jp_3251_;
}
else
{
size_t v___x_3332_; size_t v___x_3333_; lean_object* v___x_3334_; lean_object* v_snd_3335_; 
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = lean_usize_of_nat(v___x_3327_);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2649_, v___x_2647_, v___x_3324_, v___x_3332_, v___x_3333_, v___x_3330_);
lean_dec_ref(v___x_3324_);
v_snd_3335_ = lean_ctor_get(v___x_3334_, 1);
lean_inc(v_snd_3335_);
lean_dec_ref(v___x_3334_);
v___y_3252_ = v_snd_3335_;
goto v___jp_3251_;
}
}
else
{
size_t v___x_3336_; size_t v___x_3337_; lean_object* v___x_3338_; lean_object* v_snd_3339_; 
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = lean_usize_of_nat(v___x_3327_);
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2649_, v___x_2647_, v___x_3324_, v___x_3336_, v___x_3337_, v___x_3330_);
lean_dec_ref(v___x_3324_);
v_snd_3339_ = lean_ctor_get(v___x_3338_, 1);
lean_inc(v_snd_3339_);
lean_dec_ref(v___x_3338_);
v___y_3252_ = v_snd_3339_;
goto v___jp_3251_;
}
}
v___jp_3251_:
{
size_t v_sz_3253_; size_t v___x_3254_; lean_object* v___x_3255_; 
v_sz_3253_ = lean_array_size(v___y_3252_);
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3253_, v___x_3254_, v___y_3252_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3256_; lean_object* v_env_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3256_ = lean_st_ref_get(v_a_2328_);
v_env_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3257_);
lean_dec(v___x_3256_);
lean_inc_n(v_stx_2322_, 2);
v___x_3258_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3259_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3260_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3259_, v_env_3257_, v___x_3258_);
v___x_3261_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3262_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3260_, v___x_3261_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3260_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3293_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3293_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3293_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_fst_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3291_; 
v_fst_3267_ = lean_ctor_get(v_a_3263_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_a_3263_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; 
v_unused_3292_ = lean_ctor_get(v_a_3263_, 1);
lean_dec(v_unused_3292_);
v___x_3269_ = v_a_3263_;
v_isShared_3270_ = v_isSharedCheck_3291_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_fst_3267_);
lean_dec(v_a_3263_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3291_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
if (lean_obj_tag(v_fst_3267_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
lean_del_object(v___x_3265_);
v___x_3271_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3272_ = l_Lean_MessageData_ofName(v___x_3258_);
lean_inc_ref(v___x_3272_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 7);
lean_ctor_set(v___x_3269_, 1, v___x_3272_);
lean_ctor_set(v___x_3269_, 0, v___x_3271_);
v___x_3274_ = v___x_3269_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3275_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3278_ = l_Lean_indentD(v___x_3277_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3276_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3272_);
v___x_3283_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3284_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3285_;
}
}
else
{
lean_object* v_val_3287_; lean_object* v___x_3289_; 
lean_del_object(v___x_3269_);
lean_dec(v___x_3258_);
lean_dec(v_stx_2322_);
v_val_3287_ = lean_ctor_get(v_fst_3267_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v_fst_3267_, 1);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_val_3287_);
v___x_3289_ = v___x_3265_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_val_3287_);
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
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v___x_3258_);
lean_dec(v_stx_2322_);
v_a_3294_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3262_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3262_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3255_, 1);
v___x_3302_ = lean_unsigned_to_nat(3u);
v___x_3303_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3302_);
lean_dec(v_stx_2322_);
v___x_3304_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3303_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3322_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3322_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3322_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
uint8_t v_returnsEarly_3309_; lean_object* v_reassigns_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3320_; 
v_returnsEarly_3309_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*2 + 2);
v_reassigns_3310_ = lean_ctor_get(v_a_3305_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; 
v_unused_3321_ = lean_ctor_get(v_a_3305_, 0);
lean_dec(v_unused_3321_);
v___x_3312_ = v_a_3305_;
v_isShared_3313_ = v_isSharedCheck_3320_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_reassigns_3310_);
lean_dec(v_a_3305_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3320_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3250_);
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_reassigns_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3319_, sizeof(void*)*2 + 2, v_returnsEarly_3309_);
v___x_3315_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3317_; 
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*2, v___x_2647_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*2 + 1, v___x_2647_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*2 + 3, v___x_2647_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3315_);
v___x_3317_ = v___x_3307_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
else
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_unsigned_to_nat(3u);
v___x_3342_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3341_);
lean_dec(v_stx_2322_);
v___x_3343_ = l_Lean_NameSet_empty;
v___x_3344_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3344_, 0, v___x_3340_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*2, v___x_2645_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*2 + 1, v___x_2645_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*2 + 2, v___x_2645_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*2 + 3, v___x_2645_);
v___x_3345_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3342_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3354_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3350_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3344_, v_a_3346_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3350_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
else
{
lean_dec_ref_known(v___x_3344_, 2);
return v___x_3345_;
}
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; size_t v_sz_3358_; size_t v___x_3359_; lean_object* v___x_3360_; 
v___x_3355_ = lean_unsigned_to_nat(4u);
v___x_3356_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3355_);
v___x_3357_ = l_Lean_Syntax_getArgs(v___x_3356_);
lean_dec(v___x_3356_);
v_sz_3358_ = lean_array_size(v___x_3357_);
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3358_, v___x_3359_, v___x_3357_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; lean_object* v_env_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3361_ = lean_st_ref_get(v_a_2328_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
lean_inc_n(v_stx_2322_, 2);
v___x_3363_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3364_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3365_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3364_, v_env_3362_, v___x_3363_);
v___x_3366_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3367_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3365_, v___x_3366_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
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
v___x_3377_ = l_Lean_MessageData_ofName(v___x_3363_);
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
v___x_3382_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
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
v___x_3390_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3389_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3390_;
}
}
else
{
lean_object* v_val_3392_; lean_object* v___x_3394_; 
lean_del_object(v___x_3374_);
lean_dec(v___x_3363_);
lean_dec(v_stx_2322_);
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
lean_dec(v___x_3363_);
lean_dec(v_stx_2322_);
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
lean_object* v_val_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3494_; 
v_val_3407_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3409_ = v___x_3360_;
v_isShared_3410_ = v_isSharedCheck_3494_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_val_3407_);
lean_dec(v___x_3360_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3494_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v_elseSeq_x3f_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3411_ = lean_unsigned_to_nat(3u);
v___x_3412_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3411_);
v___x_3437_ = lean_unsigned_to_nat(5u);
v___x_3438_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3437_);
v___x_3439_ = l_Lean_Syntax_isNone(v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3438_);
v___x_3441_ = l_Lean_Syntax_matchesNull(v___x_3438_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v_env_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v___x_3438_);
lean_dec(v___x_3412_);
lean_del_object(v___x_3409_);
lean_dec(v_val_3407_);
v___x_3442_ = lean_st_ref_get(v_a_2328_);
v_env_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc_ref(v_env_3443_);
lean_dec(v___x_3442_);
lean_inc_n(v_stx_2322_, 2);
v___x_3444_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3445_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3446_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3445_, v_env_3443_, v___x_3444_);
v___x_3447_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3448_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3446_, v___x_3447_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3446_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3479_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_fst_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3477_; 
v_fst_3453_ = lean_ctor_get(v_a_3449_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3449_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_a_3449_, 1);
lean_dec(v_unused_3478_);
v___x_3455_ = v_a_3449_;
v_isShared_3456_ = v_isSharedCheck_3477_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_fst_3453_);
lean_dec(v_a_3449_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3477_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
if (lean_obj_tag(v_fst_3453_) == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_del_object(v___x_3451_);
v___x_3457_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3458_ = l_Lean_MessageData_ofName(v___x_3444_);
lean_inc_ref(v___x_3458_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 7);
lean_ctor_set(v___x_3455_, 1, v___x_3458_);
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3460_ = v___x_3455_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3461_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3464_ = l_Lean_indentD(v___x_3463_);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3462_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v___x_3458_);
v___x_3469_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3470_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3471_;
}
}
else
{
lean_object* v_val_3473_; lean_object* v___x_3475_; 
lean_del_object(v___x_3455_);
lean_dec(v___x_3444_);
lean_dec(v_stx_2322_);
v_val_3473_ = lean_ctor_get(v_fst_3453_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v_fst_3453_, 1);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_val_3473_);
v___x_3475_ = v___x_3451_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_val_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v___x_3444_);
lean_dec(v_stx_2322_);
v_a_3480_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3448_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3448_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v_stx_2322_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = l_Lean_Syntax_getArg(v___x_3438_, v___x_3488_);
lean_dec(v___x_3438_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3489_);
v___x_3491_ = v___x_3409_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
v_elseSeq_x3f_3414_ = v___x_3491_;
v___y_3415_ = v_a_2323_;
v___y_3416_ = v_a_2324_;
v___y_3417_ = v_a_2325_;
v___y_3418_ = v_a_2326_;
v___y_3419_ = v_a_2327_;
v___y_3420_ = v_a_2328_;
goto v___jp_3413_;
}
}
}
else
{
lean_object* v___x_3493_; 
lean_dec(v___x_3438_);
lean_del_object(v___x_3409_);
lean_dec(v_stx_2322_);
v___x_3493_ = lean_box(0);
v_elseSeq_x3f_3414_ = v___x_3493_;
v___y_3415_ = v_a_2323_;
v___y_3416_ = v_a_2324_;
v___y_3417_ = v_a_2325_;
v___y_3418_ = v_a_2326_;
v___y_3419_ = v_a_2327_;
v___y_3420_ = v_a_2328_;
goto v___jp_3413_;
}
v___jp_3413_:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; size_t v_sz_3424_; lean_object* v___x_3425_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = l_Array_reverse___redArg(v_val_3407_);
v_sz_3424_ = lean_array_size(v___x_3423_);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3423_, v_sz_3424_, v___x_3359_, v_a_3422_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec_ref(v___x_3423_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3412_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3436_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3428_, v_a_3426_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
lean_dec(v_a_3426_);
return v___x_3427_;
}
}
else
{
lean_dec(v___x_3412_);
return v___x_3425_;
}
}
else
{
lean_dec(v___x_3412_);
lean_dec(v_val_3407_);
return v___x_3421_;
}
}
}
}
}
}
else
{
lean_object* v___x_3495_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___x_3559_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3559_ = lean_unsigned_to_nat(1u);
v___x_3666_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3559_);
v___x_3667_ = l_Lean_Syntax_isNone(v___x_3666_);
if (v___x_3667_ == 0)
{
uint8_t v___x_3668_; 
lean_inc(v___x_3666_);
v___x_3668_ = l_Lean_Syntax_matchesNull(v___x_3666_, v___x_3559_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v_env_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v___x_3666_);
v___x_3669_ = lean_st_ref_get(v_a_2328_);
v_env_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc_ref(v_env_3670_);
lean_dec(v___x_3669_);
lean_inc_n(v_stx_2322_, 2);
v___x_3671_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3672_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3673_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3672_, v_env_3670_, v___x_3671_);
v___x_3674_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3675_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3673_, v___x_3674_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3673_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3706_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3706_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3706_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_fst_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3704_; 
v_fst_3680_ = lean_ctor_get(v_a_3676_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_a_3676_);
if (v_isSharedCheck_3704_ == 0)
{
lean_object* v_unused_3705_; 
v_unused_3705_ = lean_ctor_get(v_a_3676_, 1);
lean_dec(v_unused_3705_);
v___x_3682_ = v_a_3676_;
v_isShared_3683_ = v_isSharedCheck_3704_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_fst_3680_);
lean_dec(v_a_3676_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3704_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
if (lean_obj_tag(v_fst_3680_) == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_del_object(v___x_3678_);
v___x_3684_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3685_ = l_Lean_MessageData_ofName(v___x_3671_);
lean_inc_ref(v___x_3685_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 7);
lean_ctor_set(v___x_3682_, 1, v___x_3685_);
lean_ctor_set(v___x_3682_, 0, v___x_3684_);
v___x_3687_ = v___x_3682_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3688_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3691_ = l_Lean_indentD(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3689_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
lean_ctor_set(v___x_3695_, 1, v___x_3685_);
v___x_3696_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3697_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3698_;
}
}
else
{
lean_object* v_val_3700_; lean_object* v___x_3702_; 
lean_del_object(v___x_3682_);
lean_dec(v___x_3671_);
lean_dec(v_stx_2322_);
v_val_3700_ = lean_ctor_get(v_fst_3680_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v_fst_3680_, 1);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_val_3700_);
v___x_3702_ = v___x_3678_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_val_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec(v___x_3671_);
lean_dec(v_stx_2322_);
v_a_3707_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3675_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3675_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = l_Lean_Syntax_getArg(v___x_3666_, v___x_3495_);
lean_dec(v___x_3666_);
v___x_3716_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3717_ = l_Lean_Syntax_isOfKind(v___x_3715_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v_env_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3718_ = lean_st_ref_get(v_a_2328_);
v_env_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc_ref(v_env_3719_);
lean_dec(v___x_3718_);
lean_inc_n(v_stx_2322_, 2);
v___x_3720_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3721_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3722_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3721_, v_env_3719_, v___x_3720_);
v___x_3723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3724_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3722_, v___x_3723_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3722_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3755_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3755_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3755_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_fst_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3753_; 
v_fst_3729_ = lean_ctor_get(v_a_3725_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_a_3725_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v_a_3725_, 1);
lean_dec(v_unused_3754_);
v___x_3731_ = v_a_3725_;
v_isShared_3732_ = v_isSharedCheck_3753_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_fst_3729_);
lean_dec(v_a_3725_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3753_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
if (lean_obj_tag(v_fst_3729_) == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
lean_del_object(v___x_3727_);
v___x_3733_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3734_ = l_Lean_MessageData_ofName(v___x_3720_);
lean_inc_ref(v___x_3734_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 7);
lean_ctor_set(v___x_3731_, 1, v___x_3734_);
lean_ctor_set(v___x_3731_, 0, v___x_3733_);
v___x_3736_ = v___x_3731_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3737_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3740_ = l_Lean_indentD(v___x_3739_);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3738_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v___x_3734_);
v___x_3745_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3746_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3747_;
}
}
else
{
lean_object* v_val_3749_; lean_object* v___x_3751_; 
lean_del_object(v___x_3731_);
lean_dec(v___x_3720_);
lean_dec(v_stx_2322_);
v_val_3749_ = lean_ctor_get(v_fst_3729_, 0);
lean_inc(v_val_3749_);
lean_dec_ref_known(v_fst_3729_, 1);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v_val_3749_);
v___x_3751_ = v___x_3727_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_val_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v___x_3720_);
lean_dec(v_stx_2322_);
v_a_3756_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3724_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3724_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
v___y_3561_ = v_a_2323_;
v___y_3562_ = v_a_2324_;
v___y_3563_ = v_a_2325_;
v___y_3564_ = v_a_2326_;
v___y_3565_ = v_a_2327_;
v___y_3566_ = v_a_2328_;
goto v___jp_3560_;
}
}
}
else
{
lean_dec(v___x_3666_);
v___y_3561_ = v_a_2323_;
v___y_3562_ = v_a_2324_;
v___y_3563_ = v_a_2325_;
v___y_3564_ = v_a_2326_;
v___y_3565_ = v_a_2327_;
v___y_3566_ = v_a_2328_;
goto v___jp_3560_;
}
v___jp_3496_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3503_ = lean_unsigned_to_nat(6u);
v___x_3504_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3503_);
v___x_3505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3504_);
v___x_3506_ = l_Lean_Syntax_isOfKind(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v_env_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec(v___x_3504_);
v___x_3507_ = lean_st_ref_get(v___y_3502_);
v_env_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_ref(v_env_3508_);
lean_dec(v___x_3507_);
lean_inc_n(v_stx_2322_, 2);
v___x_3509_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3510_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3511_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3510_, v_env_3508_, v___x_3509_);
v___x_3512_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3513_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3511_, v___x_3512_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
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
v___x_3522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3523_ = l_Lean_MessageData_ofName(v___x_3509_);
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
v___x_3526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3529_ = l_Lean_indentD(v___x_3528_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3527_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v___x_3523_);
v___x_3534_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3535_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3536_;
}
}
else
{
lean_object* v_val_3538_; lean_object* v___x_3540_; 
lean_del_object(v___x_3520_);
lean_dec(v___x_3509_);
lean_dec(v_stx_2322_);
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
lean_dec(v___x_3509_);
lean_dec(v_stx_2322_);
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
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; size_t v_sz_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v_stx_2322_);
v___x_3553_ = l_Lean_Syntax_getArg(v___x_3504_, v___x_3495_);
lean_dec(v___x_3504_);
v___x_3554_ = l_Lean_Syntax_getArgs(v___x_3553_);
lean_dec(v___x_3553_);
v___x_3555_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_3556_ = lean_array_size(v___x_3554_);
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2641_, v___x_3554_, v_sz_3556_, v___x_3557_, v___x_3555_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec_ref(v___x_3554_);
return v___x_3558_;
}
}
v___jp_3560_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3567_ = lean_unsigned_to_nat(2u);
v___x_3568_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3567_);
v___x_3569_ = l_Lean_Syntax_isNone(v___x_3568_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
lean_inc(v___x_3568_);
v___x_3570_ = l_Lean_Syntax_matchesNull(v___x_3568_, v___x_3559_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v_env_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec(v___x_3568_);
v___x_3571_ = lean_st_ref_get(v___y_3566_);
v_env_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc_ref(v_env_3572_);
lean_dec(v___x_3571_);
lean_inc_n(v_stx_2322_, 2);
v___x_3573_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3574_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3575_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3574_, v_env_3572_, v___x_3573_);
v___x_3576_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3577_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3575_, v___x_3576_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___x_3575_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3608_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3608_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3608_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_fst_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3606_; 
v_fst_3582_ = lean_ctor_get(v_a_3578_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3578_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v_a_3578_, 1);
lean_dec(v_unused_3607_);
v___x_3584_ = v_a_3578_;
v_isShared_3585_ = v_isSharedCheck_3606_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_fst_3582_);
lean_dec(v_a_3578_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3606_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
if (lean_obj_tag(v_fst_3582_) == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
lean_del_object(v___x_3580_);
v___x_3586_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3587_ = l_Lean_MessageData_ofName(v___x_3573_);
lean_inc_ref(v___x_3587_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 7);
lean_ctor_set(v___x_3584_, 1, v___x_3587_);
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3589_ = v___x_3584_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3590_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3593_ = l_Lean_indentD(v___x_3592_);
v___x_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___x_3587_);
v___x_3598_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3599_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3600_;
}
}
else
{
lean_object* v_val_3602_; lean_object* v___x_3604_; 
lean_del_object(v___x_3584_);
lean_dec(v___x_3573_);
lean_dec(v_stx_2322_);
v_val_3602_ = lean_ctor_get(v_fst_3582_, 0);
lean_inc(v_val_3602_);
lean_dec_ref_known(v_fst_3582_, 1);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v_val_3602_);
v___x_3604_ = v___x_3580_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_val_3602_);
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
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v___x_3573_);
lean_dec(v_stx_2322_);
v_a_3609_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3577_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3577_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3617_ = l_Lean_Syntax_getArg(v___x_3568_, v___x_3495_);
lean_dec(v___x_3568_);
v___x_3618_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3619_ = l_Lean_Syntax_isOfKind(v___x_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; lean_object* v_env_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3620_ = lean_st_ref_get(v___y_3566_);
v_env_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc_ref(v_env_3621_);
lean_dec(v___x_3620_);
lean_inc_n(v_stx_2322_, 2);
v___x_3622_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3623_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3624_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3623_, v_env_3621_, v___x_3622_);
v___x_3625_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3626_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3624_, v___x_3625_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___x_3624_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3657_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3657_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3657_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v_fst_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3655_; 
v_fst_3631_ = lean_ctor_get(v_a_3627_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_a_3627_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v_a_3627_, 1);
lean_dec(v_unused_3656_);
v___x_3633_ = v_a_3627_;
v_isShared_3634_ = v_isSharedCheck_3655_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_fst_3631_);
lean_dec(v_a_3627_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3655_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
if (lean_obj_tag(v_fst_3631_) == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_del_object(v___x_3629_);
v___x_3635_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3636_ = l_Lean_MessageData_ofName(v___x_3622_);
lean_inc_ref(v___x_3636_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 7);
lean_ctor_set(v___x_3633_, 1, v___x_3636_);
lean_ctor_set(v___x_3633_, 0, v___x_3635_);
v___x_3638_ = v___x_3633_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3639_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3642_ = l_Lean_indentD(v___x_3641_);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3640_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v___x_3636_);
v___x_3647_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3648_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3649_;
}
}
else
{
lean_object* v_val_3651_; lean_object* v___x_3653_; 
lean_del_object(v___x_3633_);
lean_dec(v___x_3622_);
lean_dec(v_stx_2322_);
v_val_3651_ = lean_ctor_get(v_fst_3631_, 0);
lean_inc(v_val_3651_);
lean_dec_ref_known(v_fst_3631_, 1);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v_val_3651_);
v___x_3653_ = v___x_3629_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_val_3651_);
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
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v___x_3622_);
lean_dec(v_stx_2322_);
v_a_3658_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3626_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3626_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
v___y_3497_ = v___y_3561_;
v___y_3498_ = v___y_3562_;
v___y_3499_ = v___y_3563_;
v___y_3500_ = v___y_3564_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3566_;
goto v___jp_3496_;
}
}
}
else
{
lean_dec(v___x_3568_);
v___y_3497_ = v___y_3561_;
v___y_3498_ = v___y_3562_;
v___y_3499_ = v___y_3563_;
v___y_3500_ = v___y_3564_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3566_;
goto v___jp_3496_;
}
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___x_3764_ = lean_unsigned_to_nat(0u);
v___x_3765_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3764_);
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3765_);
v___x_3767_ = l_Lean_Syntax_isOfKind(v___x_3765_, v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3765_);
v___x_3769_ = l_Lean_Syntax_isOfKind(v___x_3765_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v_env_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec(v___x_3765_);
v___x_3770_ = lean_st_ref_get(v_a_2328_);
v_env_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc_ref(v_env_3771_);
lean_dec(v___x_3770_);
lean_inc_n(v_stx_2322_, 2);
v___x_3772_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3773_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3774_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3773_, v_env_3771_, v___x_3772_);
v___x_3775_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3776_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3774_, v___x_3775_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3774_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3807_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3807_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3807_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_fst_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3805_; 
v_fst_3781_ = lean_ctor_get(v_a_3777_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3805_ == 0)
{
lean_object* v_unused_3806_; 
v_unused_3806_ = lean_ctor_get(v_a_3777_, 1);
lean_dec(v_unused_3806_);
v___x_3783_ = v_a_3777_;
v_isShared_3784_ = v_isSharedCheck_3805_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_fst_3781_);
lean_dec(v_a_3777_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3805_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
if (lean_obj_tag(v_fst_3781_) == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
lean_del_object(v___x_3779_);
v___x_3785_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3786_ = l_Lean_MessageData_ofName(v___x_3772_);
lean_inc_ref(v___x_3786_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 7);
lean_ctor_set(v___x_3783_, 1, v___x_3786_);
lean_ctor_set(v___x_3783_, 0, v___x_3785_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3785_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3789_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3792_ = l_Lean_indentD(v___x_3791_);
v___x_3793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3790_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3786_);
v___x_3797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3798_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3799_;
}
}
else
{
lean_object* v_val_3801_; lean_object* v___x_3803_; 
lean_del_object(v___x_3783_);
lean_dec(v___x_3772_);
lean_dec(v_stx_2322_);
v_val_3801_ = lean_ctor_get(v_fst_3781_, 0);
lean_inc(v_val_3801_);
lean_dec_ref_known(v_fst_3781_, 1);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v_val_3801_);
v___x_3803_ = v___x_3779_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_val_3801_);
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
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v___x_3772_);
lean_dec(v_stx_2322_);
v_a_3808_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3776_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3776_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v___x_3816_; 
lean_dec(v_stx_2322_);
v___x_3816_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2559_, v___x_3765_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3816_;
}
}
else
{
lean_object* v___x_3817_; 
lean_dec(v_stx_2322_);
v___x_3817_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2559_, v___x_3765_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3817_;
}
}
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3818_);
v___x_3820_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
lean_inc(v___x_3819_);
v___x_3821_ = l_Lean_Syntax_isOfKind(v___x_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3822_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
lean_inc(v___x_3819_);
v___x_3823_ = l_Lean_Syntax_isOfKind(v___x_3819_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v_env_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec(v___x_3819_);
v___x_3824_ = lean_st_ref_get(v_a_2328_);
v_env_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc_ref(v_env_3825_);
lean_dec(v___x_3824_);
lean_inc_n(v_stx_2322_, 2);
v___x_3826_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3827_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3828_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3827_, v_env_3825_, v___x_3826_);
v___x_3829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3830_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3828_, v___x_3829_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3828_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3861_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3861_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3861_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v_fst_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3859_; 
v_fst_3835_ = lean_ctor_get(v_a_3831_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_a_3831_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v_a_3831_, 1);
lean_dec(v_unused_3860_);
v___x_3837_ = v_a_3831_;
v_isShared_3838_ = v_isSharedCheck_3859_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_fst_3835_);
lean_dec(v_a_3831_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3859_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
if (lean_obj_tag(v_fst_3835_) == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
lean_del_object(v___x_3833_);
v___x_3839_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3840_ = l_Lean_MessageData_ofName(v___x_3826_);
lean_inc_ref(v___x_3840_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 7);
lean_ctor_set(v___x_3837_, 1, v___x_3840_);
lean_ctor_set(v___x_3837_, 0, v___x_3839_);
v___x_3842_ = v___x_3837_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3843_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3846_ = l_Lean_indentD(v___x_3845_);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3844_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v___x_3840_);
v___x_3851_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3850_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3852_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3853_;
}
}
else
{
lean_object* v_val_3855_; lean_object* v___x_3857_; 
lean_del_object(v___x_3837_);
lean_dec(v___x_3826_);
lean_dec(v_stx_2322_);
v_val_3855_ = lean_ctor_get(v_fst_3835_, 0);
lean_inc(v_val_3855_);
lean_dec_ref_known(v_fst_3835_, 1);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v_val_3855_);
v___x_3857_ = v___x_3833_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_val_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v___x_3826_);
lean_dec(v_stx_2322_);
v_a_3862_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3830_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3830_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v___x_3870_; 
lean_dec(v_stx_2322_);
v___x_3870_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3819_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3819_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3871_, v___x_3872_, v___x_3872_, v___x_3872_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3873_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3870_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3870_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
else
{
lean_object* v___x_3882_; 
lean_dec(v_stx_2322_);
v___x_3882_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3819_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3819_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___x_3884_ = lean_box(0);
v___x_3885_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3883_, v___x_3884_, v___x_3884_, v___x_3884_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3885_;
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v_a_3886_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3882_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3882_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_isNone(v___x_3895_);
if (v___x_3896_ == 0)
{
uint8_t v___x_3897_; 
v___x_3897_ = l_Lean_Syntax_matchesNull(v___x_3895_, v___x_3894_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v_env_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3898_ = lean_st_ref_get(v_a_2328_);
v_env_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc_ref(v_env_3899_);
lean_dec(v___x_3898_);
lean_inc_n(v_stx_2322_, 2);
v___x_3900_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3901_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3902_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3901_, v_env_3899_, v___x_3900_);
v___x_3903_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3904_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3902_, v___x_3903_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3902_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3935_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3935_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3935_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v_fst_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3933_; 
v_fst_3909_ = lean_ctor_get(v_a_3905_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_a_3905_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v_a_3905_, 1);
lean_dec(v_unused_3934_);
v___x_3911_ = v_a_3905_;
v_isShared_3912_ = v_isSharedCheck_3933_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_fst_3909_);
lean_dec(v_a_3905_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3933_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
if (lean_obj_tag(v_fst_3909_) == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_del_object(v___x_3907_);
v___x_3913_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3914_ = l_Lean_MessageData_ofName(v___x_3900_);
lean_inc_ref(v___x_3914_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set_tag(v___x_3911_, 7);
lean_ctor_set(v___x_3911_, 1, v___x_3914_);
lean_ctor_set(v___x_3911_, 0, v___x_3913_);
v___x_3916_ = v___x_3911_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3917_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3920_ = l_Lean_indentD(v___x_3919_);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3918_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3914_);
v___x_3925_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3926_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3927_;
}
}
else
{
lean_object* v_val_3929_; lean_object* v___x_3931_; 
lean_del_object(v___x_3911_);
lean_dec(v___x_3900_);
lean_dec(v_stx_2322_);
v_val_3929_ = lean_ctor_get(v_fst_3909_, 0);
lean_inc(v_val_3929_);
lean_dec_ref_known(v_fst_3909_, 1);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v_val_3929_);
v___x_3931_ = v___x_3907_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_val_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v___x_3900_);
lean_dec(v_stx_2322_);
v_a_3936_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3904_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3904_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
v___y_2577_ = v_a_2323_;
v___y_2578_ = v_a_2324_;
v___y_2579_ = v_a_2325_;
v___y_2580_ = v_a_2326_;
v___y_2581_ = v_a_2327_;
v___y_2582_ = v_a_2328_;
goto v___jp_2576_;
}
}
else
{
lean_dec(v___x_3895_);
v___y_2577_ = v_a_2323_;
v___y_2578_ = v_a_2324_;
v___y_2579_ = v_a_2325_;
v___y_2580_ = v_a_2326_;
v___y_2581_ = v_a_2327_;
v___y_2582_ = v_a_2328_;
goto v___jp_2576_;
}
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_isNone(v___x_3945_);
if (v___x_3946_ == 0)
{
uint8_t v___x_3947_; 
v___x_3947_ = l_Lean_Syntax_matchesNull(v___x_3945_, v___x_3944_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; lean_object* v_env_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3948_ = lean_st_ref_get(v_a_2328_);
v_env_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_ref(v_env_3949_);
lean_dec(v___x_3948_);
lean_inc_n(v_stx_2322_, 2);
v___x_3950_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_3951_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3952_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3951_, v_env_3949_, v___x_3950_);
v___x_3953_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3954_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_3952_, v___x_3953_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_3952_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3985_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3985_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3985_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v_fst_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3983_; 
v_fst_3959_ = lean_ctor_get(v_a_3955_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_a_3955_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v_a_3955_, 1);
lean_dec(v_unused_3984_);
v___x_3961_ = v_a_3955_;
v_isShared_3962_ = v_isSharedCheck_3983_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_fst_3959_);
lean_dec(v_a_3955_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3983_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
if (lean_obj_tag(v_fst_3959_) == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
lean_del_object(v___x_3957_);
v___x_3963_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3964_ = l_Lean_MessageData_ofName(v___x_3950_);
lean_inc_ref(v___x_3964_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 7);
lean_ctor_set(v___x_3961_, 1, v___x_3964_);
lean_ctor_set(v___x_3961_, 0, v___x_3963_);
v___x_3966_ = v___x_3961_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3963_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3967_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3966_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_3970_ = l_Lean_indentD(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3968_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
lean_ctor_set(v___x_3974_, 1, v___x_3964_);
v___x_3975_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v___x_3977_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3976_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_3977_;
}
}
else
{
lean_object* v_val_3979_; lean_object* v___x_3981_; 
lean_del_object(v___x_3961_);
lean_dec(v___x_3950_);
lean_dec(v_stx_2322_);
v_val_3979_ = lean_ctor_get(v_fst_3959_, 0);
lean_inc(v_val_3979_);
lean_dec_ref_known(v_fst_3959_, 1);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v_val_3979_);
v___x_3981_ = v___x_3957_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_val_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v___x_3950_);
lean_dec(v_stx_2322_);
v_a_3986_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3954_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3954_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
v___y_2376_ = v_a_2323_;
v___y_2377_ = v_a_2324_;
v___y_2378_ = v_a_2325_;
v___y_2379_ = v_a_2326_;
v___y_2380_ = v_a_2327_;
v___y_2381_ = v_a_2328_;
goto v___jp_2375_;
}
}
else
{
lean_dec(v___x_3945_);
v___y_2376_ = v_a_2323_;
v___y_2377_ = v_a_2324_;
v___y_2378_ = v_a_2325_;
v___y_2379_ = v_a_2326_;
v___y_2380_ = v_a_2327_;
v___y_2381_ = v_a_2328_;
goto v___jp_2375_;
}
}
v___jp_2576_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2583_ = lean_unsigned_to_nat(2u);
v___x_2584_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2586_ = l_Lean_Syntax_isOfKind(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v_env_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2587_ = lean_st_ref_get(v___y_2582_);
v_env_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_ref(v_env_2588_);
lean_dec(v___x_2587_);
lean_inc_n(v_stx_2322_, 2);
v___x_2589_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2590_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2591_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2590_, v_env_2588_, v___x_2589_);
v___x_2592_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2593_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2591_, v___x_2592_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___x_2591_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2624_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2624_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2624_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_fst_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2622_; 
v_fst_2598_ = lean_ctor_get(v_a_2594_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v_a_2594_, 1);
lean_dec(v_unused_2623_);
v___x_2600_ = v_a_2594_;
v_isShared_2601_ = v_isSharedCheck_2622_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_fst_2598_);
lean_dec(v_a_2594_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2622_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
if (lean_obj_tag(v_fst_2598_) == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_del_object(v___x_2596_);
v___x_2602_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2603_ = l_Lean_MessageData_ofName(v___x_2589_);
lean_inc_ref(v___x_2603_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 7);
lean_ctor_set(v___x_2600_, 1, v___x_2603_);
lean_ctor_set(v___x_2600_, 0, v___x_2602_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2609_ = l_Lean_indentD(v___x_2608_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2607_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2603_);
v___x_2614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2615_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2616_;
}
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; 
lean_del_object(v___x_2600_);
lean_dec(v___x_2589_);
lean_dec(v_stx_2322_);
v_val_2618_ = lean_ctor_get(v_fst_2598_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v_fst_2598_, 1);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v_val_2618_);
v___x_2620_ = v___x_2596_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_val_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v___x_2589_);
lean_dec(v_stx_2322_);
v_a_2625_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2593_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2593_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_unsigned_to_nat(3u);
v___x_2634_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2633_);
lean_dec(v_stx_2322_);
v___x_2635_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2575_, v___x_2634_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2635_;
}
}
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3994_ = lean_unsigned_to_nat(0u);
v___x_3995_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_3994_);
v___x_3996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_3997_ = l_Lean_Syntax_isOfKind(v___x_3995_, v___x_3996_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v_env_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3998_ = lean_st_ref_get(v_a_2328_);
v_env_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc_ref(v_env_3999_);
lean_dec(v___x_3998_);
lean_inc_n(v_stx_2322_, 2);
v___x_4000_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4001_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4002_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4001_, v_env_3999_, v___x_4000_);
v___x_4003_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4004_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4002_, v___x_4003_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4002_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4035_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4035_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4035_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_fst_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4033_; 
v_fst_4009_ = lean_ctor_get(v_a_4005_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v_a_4005_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; 
v_unused_4034_ = lean_ctor_get(v_a_4005_, 1);
lean_dec(v_unused_4034_);
v___x_4011_ = v_a_4005_;
v_isShared_4012_ = v_isSharedCheck_4033_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_fst_4009_);
lean_dec(v_a_4005_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4033_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
if (lean_obj_tag(v_fst_4009_) == 0)
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4016_; 
lean_del_object(v___x_4007_);
v___x_4013_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4014_ = l_Lean_MessageData_ofName(v___x_4000_);
lean_inc_ref(v___x_4014_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set_tag(v___x_4011_, 7);
lean_ctor_set(v___x_4011_, 1, v___x_4014_);
lean_ctor_set(v___x_4011_, 0, v___x_4013_);
v___x_4016_ = v___x_4011_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4017_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4016_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4020_ = l_Lean_indentD(v___x_4019_);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4018_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4021_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v___x_4014_);
v___x_4025_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4026_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4027_;
}
}
else
{
lean_object* v_val_4029_; lean_object* v___x_4031_; 
lean_del_object(v___x_4011_);
lean_dec(v___x_4000_);
lean_dec(v_stx_2322_);
v_val_4029_ = lean_ctor_get(v_fst_4009_, 0);
lean_inc(v_val_4029_);
lean_dec_ref_known(v_fst_4009_, 1);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v_val_4029_);
v___x_4031_ = v___x_4007_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_val_4029_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v___x_4000_);
lean_dec(v_stx_2322_);
v_a_4036_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4004_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4004_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v___x_4044_ = lean_unsigned_to_nat(1u);
v___x_4045_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
lean_inc(v___x_4045_);
v___x_4047_ = l_Lean_Syntax_isOfKind(v___x_4045_, v___x_4046_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v_env_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec(v___x_4045_);
v___x_4048_ = lean_st_ref_get(v_a_2328_);
v_env_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc_ref(v_env_4049_);
lean_dec(v___x_4048_);
lean_inc_n(v_stx_2322_, 2);
v___x_4050_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4051_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4052_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4051_, v_env_4049_, v___x_4050_);
v___x_4053_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4054_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4052_, v___x_4053_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
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
v___x_4064_ = l_Lean_MessageData_ofName(v___x_4050_);
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
v___x_4069_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
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
v___x_4077_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4076_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4077_;
}
}
else
{
lean_object* v_val_4079_; lean_object* v___x_4081_; 
lean_del_object(v___x_4061_);
lean_dec(v___x_4050_);
lean_dec(v_stx_2322_);
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
lean_dec(v___x_4050_);
lean_dec(v_stx_2322_);
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
lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4094_ = l_Lean_Syntax_getArg(v___x_4045_, v___x_3994_);
lean_dec(v___x_4045_);
lean_inc(v___x_4094_);
v___x_4095_ = l_Lean_Syntax_matchesNull(v___x_4094_, v___x_4044_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v_env_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec(v___x_4094_);
v___x_4096_ = lean_st_ref_get(v_a_2328_);
v_env_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc_ref(v_env_4097_);
lean_dec(v___x_4096_);
lean_inc_n(v_stx_2322_, 2);
v___x_4098_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4099_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4100_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4099_, v_env_4097_, v___x_4098_);
v___x_4101_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4102_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4100_, v___x_4101_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4100_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4133_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4133_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4133_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v_fst_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4131_; 
v_fst_4107_ = lean_ctor_get(v_a_4103_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v_a_4103_);
if (v_isSharedCheck_4131_ == 0)
{
lean_object* v_unused_4132_; 
v_unused_4132_ = lean_ctor_get(v_a_4103_, 1);
lean_dec(v_unused_4132_);
v___x_4109_ = v_a_4103_;
v_isShared_4110_ = v_isSharedCheck_4131_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_fst_4107_);
lean_dec(v_a_4103_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4131_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
if (lean_obj_tag(v_fst_4107_) == 0)
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
lean_del_object(v___x_4105_);
v___x_4111_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4112_ = l_Lean_MessageData_ofName(v___x_4098_);
lean_inc_ref(v___x_4112_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 7);
lean_ctor_set(v___x_4109_, 1, v___x_4112_);
lean_ctor_set(v___x_4109_, 0, v___x_4111_);
v___x_4114_ = v___x_4109_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4115_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4114_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4118_ = l_Lean_indentD(v___x_4117_);
v___x_4119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4116_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v___x_4112_);
v___x_4123_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4124_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4125_;
}
}
else
{
lean_object* v_val_4127_; lean_object* v___x_4129_; 
lean_del_object(v___x_4109_);
lean_dec(v___x_4098_);
lean_dec(v_stx_2322_);
v_val_4127_ = lean_ctor_get(v_fst_4107_, 0);
lean_inc(v_val_4127_);
lean_dec_ref_known(v_fst_4107_, 1);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_val_4127_);
v___x_4129_ = v___x_4105_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_val_4127_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v___x_4098_);
lean_dec(v_stx_2322_);
v_a_4134_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4102_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4102_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; 
v___x_4142_ = l_Lean_Syntax_getArg(v___x_4094_, v___x_3994_);
lean_dec(v___x_4094_);
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4144_ = l_Lean_Syntax_isOfKind(v___x_4142_, v___x_4143_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v_env_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4145_ = lean_st_ref_get(v_a_2328_);
v_env_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc_ref(v_env_4146_);
lean_dec(v___x_4145_);
lean_inc_n(v_stx_2322_, 2);
v___x_4147_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4148_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4149_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4148_, v_env_4146_, v___x_4147_);
v___x_4150_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4151_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4149_, v___x_4150_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4149_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4182_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4182_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4182_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v_fst_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4180_; 
v_fst_4156_ = lean_ctor_get(v_a_4152_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_a_4152_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v_a_4152_, 1);
lean_dec(v_unused_4181_);
v___x_4158_ = v_a_4152_;
v_isShared_4159_ = v_isSharedCheck_4180_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_fst_4156_);
lean_dec(v_a_4152_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4180_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
if (lean_obj_tag(v_fst_4156_) == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
lean_del_object(v___x_4154_);
v___x_4160_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4161_ = l_Lean_MessageData_ofName(v___x_4147_);
lean_inc_ref(v___x_4161_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 7);
lean_ctor_set(v___x_4158_, 1, v___x_4161_);
lean_ctor_set(v___x_4158_, 0, v___x_4160_);
v___x_4163_ = v___x_4158_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4164_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4167_ = l_Lean_indentD(v___x_4166_);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4165_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v___x_4161_);
v___x_4172_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4171_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4173_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4174_;
}
}
else
{
lean_object* v_val_4176_; lean_object* v___x_4178_; 
lean_del_object(v___x_4158_);
lean_dec(v___x_4147_);
lean_dec(v_stx_2322_);
v_val_4176_ = lean_ctor_get(v_fst_4156_, 0);
lean_inc(v_val_4176_);
lean_dec_ref_known(v_fst_4156_, 1);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v_val_4176_);
v___x_4178_ = v___x_4154_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_val_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v___x_4147_);
lean_dec(v_stx_2322_);
v_a_4183_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4151_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4151_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_dec(v_stx_2322_);
v___x_4191_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
}
}
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4193_ = lean_unsigned_to_nat(1u);
v___x_4194_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4196_ = l_Lean_Syntax_isOfKind(v___x_4194_, v___x_4195_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4197_; lean_object* v_env_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4197_ = lean_st_ref_get(v_a_2328_);
v_env_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc_ref(v_env_4198_);
lean_dec(v___x_4197_);
lean_inc_n(v_stx_2322_, 2);
v___x_4199_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4200_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4201_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4200_, v_env_4198_, v___x_4199_);
v___x_4202_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4203_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4201_, v___x_4202_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4201_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4234_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4234_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4234_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v_fst_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4232_; 
v_fst_4208_ = lean_ctor_get(v_a_4204_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_a_4204_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; 
v_unused_4233_ = lean_ctor_get(v_a_4204_, 1);
lean_dec(v_unused_4233_);
v___x_4210_ = v_a_4204_;
v_isShared_4211_ = v_isSharedCheck_4232_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_fst_4208_);
lean_dec(v_a_4204_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4232_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
if (lean_obj_tag(v_fst_4208_) == 0)
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_del_object(v___x_4206_);
v___x_4212_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4213_ = l_Lean_MessageData_ofName(v___x_4199_);
lean_inc_ref(v___x_4213_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set_tag(v___x_4210_, 7);
lean_ctor_set(v___x_4210_, 1, v___x_4213_);
lean_ctor_set(v___x_4210_, 0, v___x_4212_);
v___x_4215_ = v___x_4210_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4212_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4216_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4219_ = l_Lean_indentD(v___x_4218_);
v___x_4220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4217_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v___x_4221_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4220_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
lean_ctor_set(v___x_4223_, 1, v___x_4213_);
v___x_4224_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4223_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4225_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4226_;
}
}
else
{
lean_object* v_val_4228_; lean_object* v___x_4230_; 
lean_del_object(v___x_4210_);
lean_dec(v___x_4199_);
lean_dec(v_stx_2322_);
v_val_4228_ = lean_ctor_get(v_fst_4208_, 0);
lean_inc(v_val_4228_);
lean_dec_ref_known(v_fst_4208_, 1);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v_val_4228_);
v___x_4230_ = v___x_4206_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_val_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v___x_4199_);
lean_dec(v_stx_2322_);
v_a_4235_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4203_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4203_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; 
v___x_4243_ = lean_unsigned_to_nat(2u);
v___x_4244_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4243_);
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4246_ = l_Lean_Syntax_isOfKind(v___x_4244_, v___x_4245_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; lean_object* v_env_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4247_ = lean_st_ref_get(v_a_2328_);
v_env_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc_ref(v_env_4248_);
lean_dec(v___x_4247_);
lean_inc_n(v_stx_2322_, 2);
v___x_4249_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4250_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4251_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4250_, v_env_4248_, v___x_4249_);
v___x_4252_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4253_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4251_, v___x_4252_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
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
v___x_4263_ = l_Lean_MessageData_ofName(v___x_4249_);
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
v___x_4268_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
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
v___x_4276_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4275_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4276_;
}
}
else
{
lean_object* v_val_4278_; lean_object* v___x_4280_; 
lean_del_object(v___x_4260_);
lean_dec(v___x_4249_);
lean_dec(v_stx_2322_);
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
lean_dec(v___x_4249_);
lean_dec(v_stx_2322_);
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
lean_object* v___x_4293_; lean_object* v___x_4294_; 
lean_dec(v_stx_2322_);
v___x_4293_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
return v___x_4294_;
}
}
}
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4295_ = lean_unsigned_to_nat(1u);
v___x_4296_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4295_);
v___x_4297_ = l_Lean_Syntax_isNone(v___x_4296_);
if (v___x_4297_ == 0)
{
uint8_t v___x_4298_; 
v___x_4298_ = l_Lean_Syntax_matchesNull(v___x_4296_, v___x_4295_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v_env_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_del_object(v___x_2359_);
v___x_4299_ = lean_st_ref_get(v_a_2328_);
v_env_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_ref(v_env_4300_);
lean_dec(v___x_4299_);
lean_inc_n(v_stx_2322_, 2);
v___x_4301_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4302_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4303_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4302_, v_env_4300_, v___x_4301_);
v___x_4304_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4305_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4303_, v___x_4304_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4303_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4336_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4336_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4336_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v_fst_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4334_; 
v_fst_4310_ = lean_ctor_get(v_a_4306_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v_a_4306_);
if (v_isSharedCheck_4334_ == 0)
{
lean_object* v_unused_4335_; 
v_unused_4335_ = lean_ctor_get(v_a_4306_, 1);
lean_dec(v_unused_4335_);
v___x_4312_ = v_a_4306_;
v_isShared_4313_ = v_isSharedCheck_4334_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_fst_4310_);
lean_dec(v_a_4306_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4334_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
if (lean_obj_tag(v_fst_4310_) == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4317_; 
lean_del_object(v___x_4308_);
v___x_4314_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4315_ = l_Lean_MessageData_ofName(v___x_4301_);
lean_inc_ref(v___x_4315_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 7);
lean_ctor_set(v___x_4312_, 1, v___x_4315_);
lean_ctor_set(v___x_4312_, 0, v___x_4314_);
v___x_4317_ = v___x_4312_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4314_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v___x_4315_);
v___x_4317_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4318_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4321_ = l_Lean_indentD(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4319_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
lean_ctor_set(v___x_4325_, 1, v___x_4315_);
v___x_4326_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4327_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4328_;
}
}
else
{
lean_object* v_val_4330_; lean_object* v___x_4332_; 
lean_del_object(v___x_4312_);
lean_dec(v___x_4301_);
lean_dec(v_stx_2322_);
v_val_4330_ = lean_ctor_get(v_fst_4310_, 0);
lean_inc(v_val_4330_);
lean_dec_ref_known(v_fst_4310_, 1);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v_val_4330_);
v___x_4332_ = v___x_4308_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_val_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v___x_4301_);
lean_dec(v_stx_2322_);
v_a_4337_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4305_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4305_);
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
else
{
v___y_2447_ = v_a_2323_;
v___y_2448_ = v_a_2324_;
v___y_2449_ = v_a_2325_;
v___y_2450_ = v_a_2326_;
v___y_2451_ = v_a_2327_;
v___y_2452_ = v_a_2328_;
goto v___jp_2446_;
}
}
else
{
lean_dec(v___x_4296_);
v___y_2447_ = v_a_2323_;
v___y_2448_ = v_a_2324_;
v___y_2449_ = v_a_2325_;
v___y_2450_ = v_a_2326_;
v___y_2451_ = v_a_2327_;
v___y_2452_ = v_a_2328_;
goto v___jp_2446_;
}
}
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
lean_del_object(v___x_2359_);
v___x_4345_ = lean_unsigned_to_nat(1u);
v___x_4346_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4345_);
lean_dec(v_stx_2322_);
v___x_4347_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4346_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4347_;
}
}
else
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
lean_del_object(v___x_2359_);
v___x_4348_ = lean_unsigned_to_nat(0u);
v___x_4349_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4348_);
lean_dec(v_stx_2322_);
v___x_4350_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_4349_);
if (lean_obj_tag(v___x_4350_) == 1)
{
lean_object* v_val_4351_; lean_object* v_snd_4352_; lean_object* v_body_4353_; lean_object* v___x_4354_; 
v_val_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_val_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v_snd_4352_ = lean_ctor_get(v_val_4351_, 1);
lean_inc(v_snd_4352_);
lean_dec(v_val_4351_);
v_body_4353_ = lean_ctor_get(v_snd_4352_, 1);
lean_inc(v_body_4353_);
lean_dec(v_snd_4352_);
v___x_4354_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_4353_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4375_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4375_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4375_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
uint8_t v_breaks_4359_; uint8_t v_continues_4360_; uint8_t v_returnsEarly_4361_; lean_object* v_reassigns_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4373_; 
v_breaks_4359_ = lean_ctor_get_uint8(v_a_4355_, sizeof(void*)*2);
v_continues_4360_ = lean_ctor_get_uint8(v_a_4355_, sizeof(void*)*2 + 1);
v_returnsEarly_4361_ = lean_ctor_get_uint8(v_a_4355_, sizeof(void*)*2 + 2);
v_reassigns_4362_ = lean_ctor_get(v_a_4355_, 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_a_4355_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v_a_4355_, 0);
lean_dec(v_unused_4374_);
v___x_4364_ = v_a_4355_;
v_isShared_4365_ = v_isSharedCheck_4373_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_reassigns_4362_);
lean_dec(v_a_4355_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4373_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4366_ = lean_unsigned_to_nat(1u);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4366_);
v___x_4368_ = v___x_4364_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4366_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_reassigns_4362_);
lean_ctor_set_uint8(v_reuseFailAlloc_4372_, sizeof(void*)*2, v_breaks_4359_);
lean_ctor_set_uint8(v_reuseFailAlloc_4372_, sizeof(void*)*2 + 1, v_continues_4360_);
lean_ctor_set_uint8(v_reuseFailAlloc_4372_, sizeof(void*)*2 + 2, v_returnsEarly_4361_);
v___x_4368_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4370_; 
lean_ctor_set_uint8(v___x_4368_, sizeof(void*)*2 + 3, v___x_2563_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4368_);
v___x_4370_ = v___x_4357_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
else
{
return v___x_4354_;
}
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_dec(v___x_4350_);
v___x_4376_ = lean_unsigned_to_nat(1u);
v___x_4377_ = l_Lean_NameSet_empty;
v___x_4378_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
lean_ctor_set_uint8(v___x_4378_, sizeof(void*)*2, v___x_2563_);
lean_ctor_set_uint8(v___x_4378_, sizeof(void*)*2 + 1, v___x_2563_);
lean_ctor_set_uint8(v___x_4378_, sizeof(void*)*2 + 2, v___x_2563_);
lean_ctor_set_uint8(v___x_4378_, sizeof(void*)*2 + 3, v___x_2563_);
v___x_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
return v___x_4379_;
}
}
}
else
{
lean_object* v___x_4380_; lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
lean_del_object(v___x_2359_);
v___x_4380_ = lean_unsigned_to_nat(0u);
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_4385_);
v___x_4387_ = l_Lean_Syntax_isNone(v___x_4386_);
if (v___x_4387_ == 0)
{
uint8_t v___x_4388_; 
v___x_4388_ = l_Lean_Syntax_matchesNull(v___x_4386_, v___x_4385_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v_env_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4389_ = lean_st_ref_get(v_a_2328_);
v_env_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc_ref(v_env_4390_);
lean_dec(v___x_4389_);
lean_inc_n(v_stx_2322_, 2);
v___x_4391_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_4392_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4393_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4392_, v_env_4390_, v___x_4391_);
v___x_4394_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4395_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_4393_, v___x_4394_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v___x_4393_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4426_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4426_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4426_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_fst_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4424_; 
v_fst_4400_ = lean_ctor_get(v_a_4396_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_a_4396_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v_a_4396_, 1);
lean_dec(v_unused_4425_);
v___x_4402_ = v_a_4396_;
v_isShared_4403_ = v_isSharedCheck_4424_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_fst_4400_);
lean_dec(v_a_4396_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4424_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
if (lean_obj_tag(v_fst_4400_) == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
lean_del_object(v___x_4398_);
v___x_4404_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4405_ = l_Lean_MessageData_ofName(v___x_4391_);
lean_inc_ref(v___x_4405_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set_tag(v___x_4402_, 7);
lean_ctor_set(v___x_4402_, 1, v___x_4405_);
lean_ctor_set(v___x_4402_, 0, v___x_4404_);
v___x_4407_ = v___x_4402_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4408_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_4411_ = l_Lean_indentD(v___x_4410_);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4409_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
lean_ctor_set(v___x_4415_, 1, v___x_4405_);
v___x_4416_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4415_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4417_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_4418_;
}
}
else
{
lean_object* v_val_4420_; lean_object* v___x_4422_; 
lean_del_object(v___x_4402_);
lean_dec(v___x_4391_);
lean_dec(v_stx_2322_);
v_val_4420_ = lean_ctor_get(v_fst_4400_, 0);
lean_inc(v_val_4420_);
lean_dec_ref_known(v_fst_4400_, 1);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v_val_4420_);
v___x_4422_ = v___x_4398_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_val_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v___x_4391_);
lean_dec(v_stx_2322_);
v_a_4427_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4395_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4395_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
else
{
lean_dec(v_stx_2322_);
goto v___jp_4381_;
}
}
else
{
lean_dec(v___x_4386_);
lean_dec(v_stx_2322_);
goto v___jp_4381_;
}
v___jp_4381_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = l_Lean_NameSet_empty;
v___x_4383_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2, v___x_2561_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2 + 1, v___x_2561_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2 + 2, v___x_2559_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*2 + 3, v___x_2559_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
}
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_del_object(v___x_2359_);
lean_dec(v_stx_2322_);
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = l_Lean_NameSet_empty;
v___x_4437_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2, v___x_2558_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2 + 1, v___x_2559_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2 + 2, v___x_2558_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2 + 3, v___x_2559_);
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_del_object(v___x_2359_);
lean_dec(v_stx_2322_);
v___x_4439_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
v___jp_2375_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2382_ = lean_unsigned_to_nat(2u);
v___x_2383_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2385_ = l_Lean_Syntax_isOfKind(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v_env_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2386_ = lean_st_ref_get(v___y_2381_);
v_env_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_env_2387_);
lean_dec(v___x_2386_);
lean_inc_n(v_stx_2322_, 2);
v___x_2388_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2389_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2390_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2389_, v_env_2387_, v___x_2388_);
v___x_2391_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2392_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2390_, v___x_2391_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___x_2390_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2423_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_fst_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2421_; 
v_fst_2397_ = lean_ctor_get(v_a_2393_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_a_2393_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v_a_2393_, 1);
lean_dec(v_unused_2422_);
v___x_2399_ = v_a_2393_;
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_fst_2397_);
lean_dec(v_a_2393_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
if (lean_obj_tag(v_fst_2397_) == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_del_object(v___x_2395_);
v___x_2401_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2402_ = l_Lean_MessageData_ofName(v___x_2388_);
lean_inc_ref(v___x_2402_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set_tag(v___x_2399_, 7);
lean_ctor_set(v___x_2399_, 1, v___x_2402_);
lean_ctor_set(v___x_2399_, 0, v___x_2401_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2405_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2408_ = l_Lean_indentD(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2406_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v___x_2402_);
v___x_2413_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2414_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v___x_2415_;
}
}
else
{
lean_object* v_val_2417_; lean_object* v___x_2419_; 
lean_del_object(v___x_2399_);
lean_dec(v___x_2388_);
lean_dec(v_stx_2322_);
v_val_2417_ = lean_ctor_get(v_fst_2397_, 0);
lean_inc(v_val_2417_);
lean_dec_ref_known(v_fst_2397_, 1);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v_val_2417_);
v___x_2419_ = v___x_2395_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_val_2417_);
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
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v___x_2388_);
lean_dec(v_stx_2322_);
v_a_2424_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2392_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2392_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2432_ = lean_unsigned_to_nat(7u);
v___x_2433_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2432_);
v___x_2434_ = lean_unsigned_to_nat(8u);
v___x_2435_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2434_);
lean_dec(v_stx_2322_);
v___x_2436_ = l_Lean_Syntax_getOptional_x3f(v___x_2435_);
lean_dec(v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_box(0);
v___y_2331_ = v___y_2381_;
v___y_2332_ = v___y_2378_;
v___y_2333_ = v___y_2377_;
v___y_2334_ = v___y_2376_;
v___y_2335_ = v___x_2433_;
v___y_2336_ = v___y_2380_;
v___y_2337_ = v___y_2379_;
v___y_2338_ = v___x_2437_;
goto v___jp_2330_;
}
else
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_val_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
v___y_2331_ = v___y_2381_;
v___y_2332_ = v___y_2378_;
v___y_2333_ = v___y_2377_;
v___y_2334_ = v___y_2376_;
v___y_2335_ = v___x_2433_;
v___y_2336_ = v___y_2380_;
v___y_2337_ = v___y_2379_;
v___y_2338_ = v___x_2443_;
goto v___jp_2330_;
}
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2453_ = lean_unsigned_to_nat(2u);
v___x_2454_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2456_ = l_Lean_Syntax_isOfKind(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v_env_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_del_object(v___x_2359_);
v___x_2457_ = lean_st_ref_get(v___y_2452_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc_ref(v_env_2458_);
lean_dec(v___x_2457_);
lean_inc_n(v_stx_2322_, 2);
v___x_2459_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2460_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2461_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2460_, v_env_2458_, v___x_2459_);
v___x_2462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2463_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2461_, v___x_2462_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___x_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2494_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2494_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2494_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_fst_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2492_; 
v_fst_2468_ = lean_ctor_get(v_a_2464_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_a_2464_, 1);
lean_dec(v_unused_2493_);
v___x_2470_ = v_a_2464_;
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_fst_2468_);
lean_dec(v_a_2464_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
if (lean_obj_tag(v_fst_2468_) == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_del_object(v___x_2466_);
v___x_2472_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2473_ = l_Lean_MessageData_ofName(v___x_2459_);
lean_inc_ref(v___x_2473_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 7);
lean_ctor_set(v___x_2470_, 1, v___x_2473_);
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2475_ = v___x_2470_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2476_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2479_ = l_Lean_indentD(v___x_2478_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2477_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___x_2473_);
v___x_2484_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2485_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2486_;
}
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2490_; 
lean_del_object(v___x_2470_);
lean_dec(v___x_2459_);
lean_dec(v_stx_2322_);
v_val_2488_ = lean_ctor_get(v_fst_2468_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v_fst_2468_, 1);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v_val_2488_);
v___x_2490_ = v___x_2466_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_val_2488_);
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
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v___x_2459_);
lean_dec(v_stx_2322_);
v_a_2495_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2463_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2463_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2503_ = lean_unsigned_to_nat(3u);
v___x_2504_ = l_Lean_Syntax_getArg(v_stx_2322_, v___x_2503_);
v___x_2505_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2506_ = l_Lean_Syntax_isOfKind(v___x_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v_env_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_del_object(v___x_2359_);
v___x_2507_ = lean_st_ref_get(v___y_2452_);
v_env_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_ref(v_env_2508_);
lean_dec(v___x_2507_);
lean_inc_n(v_stx_2322_, 2);
v___x_2509_ = l_Lean_Syntax_getKind(v_stx_2322_);
v___x_2510_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2511_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2510_, v_env_2508_, v___x_2509_);
v___x_2512_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2513_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2322_, v___x_2511_, v___x_2512_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___x_2511_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2544_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2544_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2544_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_fst_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2542_; 
v_fst_2518_ = lean_ctor_get(v_a_2514_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_a_2514_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v_a_2514_, 1);
lean_dec(v_unused_2543_);
v___x_2520_ = v_a_2514_;
v_isShared_2521_ = v_isSharedCheck_2542_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_fst_2518_);
lean_dec(v_a_2514_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2542_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
if (lean_obj_tag(v_fst_2518_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_del_object(v___x_2516_);
v___x_2522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2523_ = l_Lean_MessageData_ofName(v___x_2509_);
lean_inc_ref(v___x_2523_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 7);
lean_ctor_set(v___x_2520_, 1, v___x_2523_);
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_MessageData_ofSyntax(v_stx_2322_);
v___x_2529_ = l_Lean_indentD(v___x_2528_);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2523_);
v___x_2534_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2535_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2536_;
}
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2540_; 
lean_del_object(v___x_2520_);
lean_dec(v___x_2509_);
lean_dec(v_stx_2322_);
v_val_2538_ = lean_ctor_get(v_fst_2518_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_fst_2518_, 1);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v_val_2538_);
v___x_2540_ = v___x_2516_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_val_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v___x_2509_);
lean_dec(v_stx_2322_);
v_a_2545_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2513_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2513_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_dec(v_stx_2322_);
v___x_2553_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2553_);
v___x_2555_ = v___x_2359_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec(v_stx_2322_);
v_a_4442_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_2356_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_2356_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
v___jp_2330_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___y_2335_);
v___x_2342_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2339_, v___x_2340_, v___x_2341_, v___y_2338_, v___y_2334_, v___y_2333_, v___y_2332_, v___y_2337_, v___y_2336_, v___y_2331_);
return v___x_2342_;
}
v___jp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2344_, v_bodyInfo_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
v___jp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2349_, v_bodyInfo_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4450_, size_t v_sz_4451_, size_t v_i_4452_, lean_object* v_b_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
uint8_t v___x_4461_; 
v___x_4461_ = lean_usize_dec_lt(v_i_4452_, v_sz_4451_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; 
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v_b_4453_);
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4464_; 
v_a_4463_ = lean_array_uget_borrowed(v_as_4450_, v_i_4452_);
lean_inc(v_a_4463_);
v___x_4464_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4463_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4466_; size_t v___x_4467_; size_t v___x_4468_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 1);
v___x_4466_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_4453_, v_a_4465_);
v___x_4467_ = ((size_t)1ULL);
v___x_4468_ = lean_usize_add(v_i_4452_, v___x_4467_);
v_i_4452_ = v___x_4468_;
v_b_4453_ = v___x_4466_;
goto _start;
}
else
{
lean_dec_ref(v_b_4453_);
return v___x_4464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_info_4478_; lean_object* v___x_4479_; size_t v_sz_4480_; size_t v___x_4481_; lean_object* v___x_4482_; 
v_info_4478_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4479_ = l_Lean_Parser_Term_getDoElems(v_stx_4470_);
v_sz_4480_ = lean_array_size(v___x_4479_);
v___x_4481_ = ((size_t)0ULL);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4479_, v_sz_4480_, v___x_4481_, v_info_4478_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_);
lean_dec_ref(v___x_4479_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec_ref(v_a_4493_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4501_, lean_object* v_sz_4502_, lean_object* v_i_4503_, lean_object* v_b_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
size_t v_sz_boxed_4512_; size_t v_i_boxed_4513_; lean_object* v_res_4514_; 
v_sz_boxed_4512_ = lean_unbox_usize(v_sz_4502_);
lean_dec(v_sz_4502_);
v_i_boxed_4513_ = lean_unbox_usize(v_i_4503_);
lean_dec(v_i_4503_);
v_res_4514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4501_, v_sz_boxed_4512_, v_i_boxed_4513_, v_b_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec_ref(v_as_4501_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4515_, lean_object* v_sz_4516_, lean_object* v_i_4517_, lean_object* v_b_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
size_t v_sz_boxed_4526_; size_t v_i_boxed_4527_; lean_object* v_res_4528_; 
v_sz_boxed_4526_ = lean_unbox_usize(v_sz_4516_);
lean_dec(v_sz_4516_);
v_i_boxed_4527_ = lean_unbox_usize(v_i_4517_);
lean_dec(v_i_4517_);
v_res_4528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4515_, v_sz_boxed_4526_, v_i_boxed_4527_, v_b_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec_ref(v_as_4515_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4529_, lean_object* v_rhs_x3f_4530_, lean_object* v_otherwise_x3f_4531_, lean_object* v_body_x3f_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4529_, v_rhs_x3f_4530_, v_otherwise_x3f_4531_, v_body_x3f_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4541_, lean_object* v_as_4542_, lean_object* v_sz_4543_, lean_object* v_i_4544_, lean_object* v_b_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
uint8_t v___x_284046__boxed_4553_; size_t v_sz_boxed_4554_; size_t v_i_boxed_4555_; lean_object* v_res_4556_; 
v___x_284046__boxed_4553_ = lean_unbox(v___x_4541_);
v_sz_boxed_4554_ = lean_unbox_usize(v_sz_4543_);
lean_dec(v_sz_4543_);
v_i_boxed_4555_ = lean_unbox_usize(v_i_4544_);
lean_dec(v_i_4544_);
v_res_4556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_284046__boxed_4553_, v_as_4542_, v_sz_boxed_4554_, v_i_boxed_4555_, v_b_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v_as_4542_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4557_, lean_object* v_as_4558_, lean_object* v_sz_4559_, lean_object* v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
uint8_t v___x_284097__boxed_4569_; size_t v_sz_boxed_4570_; size_t v_i_boxed_4571_; lean_object* v_res_4572_; 
v___x_284097__boxed_4569_ = lean_unbox(v___x_4557_);
v_sz_boxed_4570_ = lean_unbox_usize(v_sz_4559_);
lean_dec(v_sz_4559_);
v_i_boxed_4571_ = lean_unbox_usize(v_i_4560_);
lean_dec(v_i_4560_);
v_res_4572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_284097__boxed_4569_, v_as_4558_, v_sz_boxed_4570_, v_i_boxed_4571_, v_b_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v_as_4558_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4573_, lean_object* v_sz_4574_, lean_object* v_i_4575_, lean_object* v_b_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_sz_boxed_4584_; size_t v_i_boxed_4585_; lean_object* v_res_4586_; 
v_sz_boxed_4584_ = lean_unbox_usize(v_sz_4574_);
lean_dec(v_sz_4574_);
v_i_boxed_4585_ = lean_unbox_usize(v_i_4575_);
lean_dec(v_i_4575_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4573_, v_sz_boxed_4584_, v_i_boxed_4585_, v_b_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_as_4573_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4587_, lean_object* v_decl_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
uint8_t v_reassignment_boxed_4596_; lean_object* v_res_4597_; 
v_reassignment_boxed_4596_ = lean_unbox(v_reassignment_4587_);
v_res_4597_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4596_, v_decl_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4625_, lean_object* v_ref_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4626_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4635_, lean_object* v_ref_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4635_, v_ref_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4645_, lean_object* v_x_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4655_, lean_object* v_x_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4655_, v_x_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4665_, lean_object* v_as_4666_, lean_object* v_as_x27_4667_, lean_object* v_b_4668_, lean_object* v_a_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4665_, v_as_x27_4667_, v_b_4668_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4678_, lean_object* v_as_4679_, lean_object* v_as_x27_4680_, lean_object* v_b_4681_, lean_object* v_a_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4678_, v_as_4679_, v_as_x27_4680_, v_b_4681_, v_a_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v_as_x27_4680_);
lean_dec(v_as_4679_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4691_, lean_object* v_msg_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4701_, lean_object* v_msg_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4701_, v_msg_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4711_, lean_object* v_msg_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4711_, v_msg_4712_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4721_, lean_object* v_msg_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4721_, v_msg_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4731_, lean_object* v_as_x27_4732_, lean_object* v_b_4733_, lean_object* v_a_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4732_, v_b_4733_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4743_, lean_object* v_as_x27_4744_, lean_object* v_b_4745_, lean_object* v_a_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4743_, v_as_x27_4744_, v_b_4745_, v_a_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v_as_x27_4744_);
lean_dec(v_as_4743_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4755_, lean_object* v_ref_4756_, lean_object* v_msg_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4756_, v_msg_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4766_, lean_object* v_ref_4767_, lean_object* v_msg_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4766_, v_ref_4767_, v_msg_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec(v_ref_4767_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4777_, lean_object* v_macroStack_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4777_, v_macroStack_4778_, v___y_4783_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4787_, lean_object* v_macroStack_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4787_, v_macroStack_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4797_, lean_object* v_m_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4798_, v_a_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4801_, lean_object* v_m_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4801_, v_m_4802_, v_a_4803_);
lean_dec(v_a_4803_);
lean_dec_ref(v_m_4802_);
return v_res_4804_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4805_, lean_object* v_x_4806_, lean_object* v_x_4807_){
_start:
{
uint8_t v___x_4808_; 
v___x_4808_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4806_, v_x_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4809_, lean_object* v_x_4810_, lean_object* v_x_4811_){
_start:
{
uint8_t v_res_4812_; lean_object* v_r_4813_; 
v_res_4812_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4809_, v_x_4810_, v_x_4811_);
lean_dec_ref(v_x_4811_);
lean_dec_ref(v_x_4810_);
v_r_4813_ = lean_box(v_res_4812_);
return v_r_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4814_, lean_object* v_a_4815_, lean_object* v_x_4816_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4815_, v_x_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4818_, lean_object* v_a_4819_, lean_object* v_x_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4818_, v_a_4819_, v_x_4820_);
lean_dec(v_x_4820_);
lean_dec(v_a_4819_);
return v_res_4821_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4822_, lean_object* v_x_4823_, size_t v_x_4824_, lean_object* v_x_4825_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4823_, v_x_4824_, v_x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4827_, lean_object* v_x_4828_, lean_object* v_x_4829_, lean_object* v_x_4830_){
_start:
{
size_t v_x_289863__boxed_4831_; uint8_t v_res_4832_; lean_object* v_r_4833_; 
v_x_289863__boxed_4831_ = lean_unbox_usize(v_x_4829_);
lean_dec(v_x_4829_);
v_res_4832_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4827_, v_x_4828_, v_x_289863__boxed_4831_, v_x_4830_);
lean_dec_ref(v_x_4830_);
lean_dec_ref(v_x_4828_);
v_r_4833_ = lean_box(v_res_4832_);
return v_r_4833_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4834_, lean_object* v_keys_4835_, lean_object* v_vals_4836_, lean_object* v_heq_4837_, lean_object* v_i_4838_, lean_object* v_k_4839_){
_start:
{
uint8_t v___x_4840_; 
v___x_4840_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4835_, v_i_4838_, v_k_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4841_, lean_object* v_keys_4842_, lean_object* v_vals_4843_, lean_object* v_heq_4844_, lean_object* v_i_4845_, lean_object* v_k_4846_){
_start:
{
uint8_t v_res_4847_; lean_object* v_r_4848_; 
v_res_4847_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4841_, v_keys_4842_, v_vals_4843_, v_heq_4844_, v_i_4845_, v_k_4846_);
lean_dec_ref(v_k_4846_);
lean_dec_ref(v_vals_4843_);
lean_dec_ref(v_keys_4842_);
v_r_4848_ = lean_box(v_res_4847_);
return v_r_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
lean_dec_ref(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
return v_res_4884_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
