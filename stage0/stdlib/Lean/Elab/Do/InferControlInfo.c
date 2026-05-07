// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
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
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 249, .m_capacity = 249, .m_length = 246, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `TSyntax \\`doElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(105) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(113) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1;
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
lean_object* v___y_25_; uint8_t v___y_26_; uint8_t v___y_27_; uint8_t v___y_28_; lean_object* v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_25_);
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
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_26_);
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
v___y_25_ = v_reassigns_41_;
v___y_26_ = v___y_36_;
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
v___y_25_ = v_reassigns_43_;
v___y_26_ = v___y_36_;
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
lean_object* v___y_57_; uint8_t v___y_58_; uint8_t v___y_59_; lean_object* v___y_60_; uint8_t v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_57_, v___y_62_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_60_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_58_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_61_);
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
v___y_57_ = v_reassigns_71_;
v___y_58_ = v___y_73_;
v___y_59_ = v___y_75_;
v___y_60_ = v___x_79_;
v___y_61_ = v___y_74_;
v___y_62_ = v_reassigns_78_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v_reassigns_71_;
v___y_58_ = v___y_73_;
v___y_59_ = v___y_75_;
v___y_60_ = v___x_79_;
v___y_61_ = v___y_74_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
v___x_241_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
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
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
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
lean_dec_ref(v___x_342_);
if (lean_obj_tag(v_val_344_) == 1)
{
uint8_t v_v_345_; 
v_v_345_ = lean_ctor_get_uint8(v_val_344_, 0);
lean_dec_ref(v_val_344_);
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
lean_object* v_options_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_options_360_ = lean_ctor_get(v___y_358_, 2);
v___x_361_ = l_Lean_Elab_pp_macroStack;
v___x_362_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_macroStack_357_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_msgData_356_);
return v___x_363_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_383_, lean_object* v_macroStack_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_383_, v_macroStack_384_, v___y_385_);
lean_dec_ref(v___y_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v_macroStack_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 5);
v___x_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_388_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v_macroStack_399_ = lean_ctor_get(v___y_389_, 1);
v___x_400_ = l_Lean_Elab_getBetterRef(v_ref_396_, v_macroStack_399_);
lean_inc(v_macroStack_399_);
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_398_, v_macroStack_399_, v___y_393_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v_b_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
v___x_425_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
lean_inc(v___x_425_);
v___x_426_ = l_Lean_NameSet_insert(v_b_423_, v___x_425_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_421_, v___x_427_);
v_i_421_ = v___x_428_;
v_b_423_ = v___x_426_;
goto _start;
}
else
{
return v_b_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_430_, lean_object* v_i_431_, lean_object* v_stop_432_, lean_object* v_b_433_){
_start:
{
size_t v_i_boxed_434_; size_t v_stop_boxed_435_; lean_object* v_res_436_; 
v_i_boxed_434_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_stop_boxed_435_ = lean_unbox_usize(v_stop_432_);
lean_dec(v_stop_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_430_, v_i_boxed_434_, v_stop_boxed_435_, v_b_433_);
lean_dec_ref(v_as_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_437_, size_t v_i_438_, lean_object* v_bs_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_440_ == 0)
{
return v_bs_439_;
}
else
{
lean_object* v_v_441_; lean_object* v___x_442_; lean_object* v_bs_x27_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_v_441_ = lean_array_uget(v_bs_439_, v_i_438_);
v___x_442_ = lean_unsigned_to_nat(0u);
v_bs_x27_443_ = lean_array_uset(v_bs_439_, v_i_438_, v___x_442_);
v___x_444_ = l_Lean_TSyntax_getId(v_v_441_);
lean_dec(v_v_441_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_438_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_443_, v_i_438_, v___x_444_);
v_i_438_ = v___x_446_;
v_bs_439_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_452_, v_i_boxed_453_, v_bs_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_bs_465_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v_bs_x27_469_; lean_object* v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v_bs_x27_469_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_468_);
v___x_470_ = lean_box(0);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_464_, v___x_471_);
v___x_473_ = lean_array_uset(v_bs_x27_469_, v_i_464_, v___x_470_);
v_i_464_ = v___x_472_;
v_bs_465_ = v___x_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_481_, uint8_t v___x_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___y_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_492_ == 0)
{
lean_object* v_fst_493_; uint8_t v___x_494_; 
v_fst_493_ = lean_ctor_get(v_b_486_, 0);
v___x_494_ = lean_unbox(v_fst_493_);
if (v___x_494_ == 0)
{
lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_snd_495_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_504_);
v___x_497_ = v_b_486_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_dec(v_b_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(v___x_481_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_snd_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
v___y_488_ = v___x_501_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_snd_505_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_516_);
v___x_507_ = v_b_486_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_dec(v_b_486_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
lean_inc(v___x_509_);
v___x_510_ = lean_array_push(v_snd_505_, v___x_509_);
v___x_511_ = lean_box(v___x_482_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_510_);
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_510_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_488_ = v___x_513_;
goto v___jp_487_;
}
}
}
}
else
{
return v_b_486_;
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_484_, v___x_489_);
v_i_484_ = v___x_490_;
v_b_486_ = v___y_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_, lean_object* v_b_522_){
_start:
{
uint8_t v___x_280970__boxed_523_; uint8_t v___x_280971__boxed_524_; size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v___x_280970__boxed_523_ = lean_unbox(v___x_517_);
v___x_280971__boxed_524_ = lean_unbox(v___x_518_);
v_i_boxed_525_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_280970__boxed_523_, v___x_280971__boxed_524_, v_as_519_, v_i_boxed_525_, v_stop_boxed_526_, v_b_522_);
lean_dec_ref(v_as_519_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_528_, lean_object* v_declName_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_532_; lean_object* v_env_533_; lean_object* v___x_534_; uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_532_ = 0;
v_env_533_ = l_Lean_Environment_setExporting(v_env_528_, v___x_532_);
lean_inc(v_declName_529_);
v___x_534_ = l_Lean_mkPrivateName(v_env_533_, v_declName_529_);
v___x_535_ = 1;
lean_inc_ref(v_env_533_);
v___x_536_ = l_Lean_Environment_contains(v_env_533_, v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = l_Lean_privateToUserName(v_declName_529_);
v___x_538_ = l_Lean_Environment_contains(v_env_533_, v___x_537_, v___x_535_);
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___y_531_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_env_533_);
lean_dec(v_declName_529_);
v___x_541_ = lean_box(v___x_536_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_531_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_543_, lean_object* v_declName_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_543_, v_declName_544_, v___y_545_, v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l_Lean_maxRecDepthErrorMessage;
v___x_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_556_ = l_Lean_MessageData_ofFormat(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_558_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_559_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_560_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_ref_560_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_570_);
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_570_);
lean_ctor_set(v___x_571_, 1, v___y_569_);
return v___x_571_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_572_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_572_);
lean_ctor_set(v___x_573_, 1, v___y_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_574_, v___y_575_);
lean_dec_ref(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_577_, lean_object* v_stx_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_577_, v_stx_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
if (lean_obj_tag(v_a_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_a_583_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_592_);
v___x_585_ = v___x_581_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_621_; 
v_val_593_ = lean_ctor_get(v_a_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_595_ = v_a_582_;
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v_a_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_snd_597_; 
v_snd_597_ = lean_ctor_get(v_val_593_, 1);
lean_inc(v_snd_597_);
lean_dec(v_val_593_);
if (lean_obj_tag(v_snd_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_del_object(v___x_595_);
v_a_598_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_598_);
lean_dec_ref(v___x_581_);
v_a_599_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_snd_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_snd_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_604_, v_a_598_);
lean_dec_ref(v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_620_; 
v_a_608_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_608_);
lean_dec_ref(v___x_581_);
v_a_609_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_611_ = v_snd_597_;
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v_snd_597_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_a_609_);
v___x_614_ = v___x_595_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_616_, v_a_608_);
lean_dec_ref(v___x_616_);
return v___x_617_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_622_ = lean_ctor_get(v___x_581_, 0);
v_a_623_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_581_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_581_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_631_, lean_object* v_stx_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_631_, v_stx_632_, v___y_633_, v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_fileName_645_; lean_object* v_fileMap_646_; lean_object* v_options_647_; lean_object* v_currRecDepth_648_; lean_object* v_maxRecDepth_649_; lean_object* v_ref_650_; lean_object* v_currNamespace_651_; lean_object* v_openDecls_652_; lean_object* v_initHeartbeats_653_; lean_object* v_maxHeartbeats_654_; lean_object* v_quotContext_655_; lean_object* v_currMacroScope_656_; uint8_t v_diag_657_; lean_object* v_cancelTk_x3f_658_; uint8_t v_suppressElabErrors_659_; lean_object* v_inheritedTraceOptions_660_; lean_object* v_ref_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_fileName_645_ = lean_ctor_get(v___y_642_, 0);
v_fileMap_646_ = lean_ctor_get(v___y_642_, 1);
v_options_647_ = lean_ctor_get(v___y_642_, 2);
v_currRecDepth_648_ = lean_ctor_get(v___y_642_, 3);
v_maxRecDepth_649_ = lean_ctor_get(v___y_642_, 4);
v_ref_650_ = lean_ctor_get(v___y_642_, 5);
v_currNamespace_651_ = lean_ctor_get(v___y_642_, 6);
v_openDecls_652_ = lean_ctor_get(v___y_642_, 7);
v_initHeartbeats_653_ = lean_ctor_get(v___y_642_, 8);
v_maxHeartbeats_654_ = lean_ctor_get(v___y_642_, 9);
v_quotContext_655_ = lean_ctor_get(v___y_642_, 10);
v_currMacroScope_656_ = lean_ctor_get(v___y_642_, 11);
v_diag_657_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14);
v_cancelTk_x3f_658_ = lean_ctor_get(v___y_642_, 12);
v_suppressElabErrors_659_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_660_ = lean_ctor_get(v___y_642_, 13);
v_ref_661_ = l_Lean_replaceRef(v_ref_636_, v_ref_650_);
lean_inc_ref(v_inheritedTraceOptions_660_);
lean_inc(v_cancelTk_x3f_658_);
lean_inc(v_currMacroScope_656_);
lean_inc(v_quotContext_655_);
lean_inc(v_maxHeartbeats_654_);
lean_inc(v_initHeartbeats_653_);
lean_inc(v_openDecls_652_);
lean_inc(v_currNamespace_651_);
lean_inc(v_maxRecDepth_649_);
lean_inc(v_currRecDepth_648_);
lean_inc_ref(v_options_647_);
lean_inc_ref(v_fileMap_646_);
lean_inc_ref(v_fileName_645_);
v___x_662_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_662_, 0, v_fileName_645_);
lean_ctor_set(v___x_662_, 1, v_fileMap_646_);
lean_ctor_set(v___x_662_, 2, v_options_647_);
lean_ctor_set(v___x_662_, 3, v_currRecDepth_648_);
lean_ctor_set(v___x_662_, 4, v_maxRecDepth_649_);
lean_ctor_set(v___x_662_, 5, v_ref_661_);
lean_ctor_set(v___x_662_, 6, v_currNamespace_651_);
lean_ctor_set(v___x_662_, 7, v_openDecls_652_);
lean_ctor_set(v___x_662_, 8, v_initHeartbeats_653_);
lean_ctor_set(v___x_662_, 9, v_maxHeartbeats_654_);
lean_ctor_set(v___x_662_, 10, v_quotContext_655_);
lean_ctor_set(v___x_662_, 11, v_currMacroScope_656_);
lean_ctor_set(v___x_662_, 12, v_cancelTk_x3f_658_);
lean_ctor_set(v___x_662_, 13, v_inheritedTraceOptions_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*14, v_diag_657_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*14 + 1, v_suppressElabErrors_659_);
v___x_663_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___x_662_, v___y_643_);
lean_dec_ref(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_664_, v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_ref_664_);
return v_res_673_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_674_; double v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_float_of_nat(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_ref_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_732_; 
v_ref_686_ = lean_ctor_get(v___y_683_, 5);
v___x_687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_732_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_732_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_732_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v_traceState_693_; lean_object* v_env_694_; lean_object* v_nextMacroScope_695_; lean_object* v_ngen_696_; lean_object* v_auxDeclNGen_697_; lean_object* v_cache_698_; lean_object* v_messages_699_; lean_object* v_infoState_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_731_; 
v___x_692_ = lean_st_ref_take(v___y_684_);
v_traceState_693_ = lean_ctor_get(v___x_692_, 4);
v_env_694_ = lean_ctor_get(v___x_692_, 0);
v_nextMacroScope_695_ = lean_ctor_get(v___x_692_, 1);
v_ngen_696_ = lean_ctor_get(v___x_692_, 2);
v_auxDeclNGen_697_ = lean_ctor_get(v___x_692_, 3);
v_cache_698_ = lean_ctor_get(v___x_692_, 5);
v_messages_699_ = lean_ctor_get(v___x_692_, 6);
v_infoState_700_ = lean_ctor_get(v___x_692_, 7);
v_snapshotTasks_701_ = lean_ctor_get(v___x_692_, 8);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_731_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_700_);
lean_inc(v_messages_699_);
lean_inc(v_cache_698_);
lean_inc(v_traceState_693_);
lean_inc(v_auxDeclNGen_697_);
lean_inc(v_ngen_696_);
lean_inc(v_nextMacroScope_695_);
lean_inc(v_env_694_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint64_t v_tid_705_; lean_object* v_traces_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_730_; 
v_tid_705_ = lean_ctor_get_uint64(v_traceState_693_, sizeof(void*)*1);
v_traces_706_ = lean_ctor_get(v_traceState_693_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_traceState_693_);
if (v_isSharedCheck_730_ == 0)
{
v___x_708_ = v_traceState_693_;
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_traces_706_);
lean_dec(v_traceState_693_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; double v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_710_ = lean_box(0);
v___x_711_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_712_ = 0;
v___x_713_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_714_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_714_, 0, v_cls_679_);
lean_ctor_set(v___x_714_, 1, v___x_710_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
lean_ctor_set_float(v___x_714_, sizeof(void*)*3, v___x_711_);
lean_ctor_set_float(v___x_714_, sizeof(void*)*3 + 8, v___x_711_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*3 + 16, v___x_712_);
v___x_715_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_716_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v_a_688_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_inc(v_ref_686_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_ref_686_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_PersistentArray_push___redArg(v_traces_706_, v___x_717_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_718_);
v___x_720_ = v___x_708_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_718_);
lean_ctor_set_uint64(v_reuseFailAlloc_729_, sizeof(void*)*1, v_tid_705_);
v___x_720_ = v_reuseFailAlloc_729_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_720_);
v___x_722_ = v___x_703_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_env_694_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_nextMacroScope_695_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_ngen_696_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_auxDeclNGen_697_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_cache_698_);
lean_ctor_set(v_reuseFailAlloc_728_, 6, v_messages_699_);
lean_ctor_set(v_reuseFailAlloc_728_, 7, v_infoState_700_);
lean_ctor_set(v_reuseFailAlloc_728_, 8, v_snapshotTasks_701_);
v___x_722_ = v_reuseFailAlloc_728_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_723_ = lean_st_ref_set(v___y_684_, v___x_722_);
v___x_724_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_724_);
v___x_726_ = v___x_690_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_733_, v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
if (lean_obj_tag(v_as_744_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v_options_754_; uint8_t v_hasTrace_755_; 
v_options_754_ = lean_ctor_get(v___y_749_, 2);
v_hasTrace_755_ = lean_ctor_get_uint8(v_options_754_, sizeof(void*)*1);
if (v_hasTrace_755_ == 0)
{
lean_object* v_tail_756_; 
v_tail_756_ = lean_ctor_get(v_as_744_, 1);
lean_inc(v_tail_756_);
lean_dec_ref(v_as_744_);
v_as_744_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v_head_758_; lean_object* v_tail_759_; lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v_inheritedTraceOptions_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_head_758_ = lean_ctor_get(v_as_744_, 0);
lean_inc(v_head_758_);
v_tail_759_ = lean_ctor_get(v_as_744_, 1);
lean_inc(v_tail_759_);
lean_dec_ref(v_as_744_);
v_fst_760_ = lean_ctor_get(v_head_758_, 0);
lean_inc_n(v_fst_760_, 2);
v_snd_761_ = lean_ctor_get(v_head_758_, 1);
lean_inc(v_snd_761_);
lean_dec(v_head_758_);
v_inheritedTraceOptions_762_ = lean_ctor_get(v___y_749_, 13);
v___x_763_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_764_ = l_Lean_Name_append(v___x_763_, v_fst_760_);
v___x_765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_754_, v___x_764_);
lean_dec(v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_snd_761_);
lean_dec(v_fst_760_);
v_as_744_ = v_tail_759_;
goto _start;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_767_, 0, v_snd_761_);
v___x_768_ = l_Lean_MessageData_ofFormat(v___x_767_);
v___x_769_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_760_, v___x_768_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_dec_ref(v___x_769_);
v_as_744_ = v_tail_759_;
goto _start;
}
else
{
lean_dec(v_tail_759_);
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; uint8_t v___x_786_; 
v_key_783_ = lean_ctor_get(v_x_781_, 0);
v_value_784_ = lean_ctor_get(v_x_781_, 1);
v_tail_785_ = lean_ctor_get(v_x_781_, 2);
v___x_786_ = lean_name_eq(v_key_783_, v_a_780_);
if (v___x_786_ == 0)
{
v_x_781_ = v_tail_785_;
goto _start;
}
else
{
lean_object* v___x_788_; 
lean_inc(v_value_784_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_value_784_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_a_789_);
return v_res_791_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_792_; uint64_t v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1723u);
v___x_793_ = lean_uint64_of_nat(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_buckets_796_; lean_object* v___x_797_; uint64_t v___y_799_; 
v_buckets_796_ = lean_ctor_get(v_m_794_, 1);
v___x_797_ = lean_array_get_size(v_buckets_796_);
if (lean_obj_tag(v_a_795_) == 0)
{
uint64_t v___x_813_; 
v___x_813_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___closed__0);
v___y_799_ = v___x_813_;
goto v___jp_798_;
}
else
{
uint64_t v_hash_814_; 
v_hash_814_ = lean_ctor_get_uint64(v_a_795_, sizeof(void*)*2);
v___y_799_ = v_hash_814_;
goto v___jp_798_;
}
v___jp_798_:
{
uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v_fold_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_800_ = 32ULL;
v___x_801_ = lean_uint64_shift_right(v___y_799_, v___x_800_);
v_fold_802_ = lean_uint64_xor(v___y_799_, v___x_801_);
v___x_803_ = 16ULL;
v___x_804_ = lean_uint64_shift_right(v_fold_802_, v___x_803_);
v___x_805_ = lean_uint64_xor(v_fold_802_, v___x_804_);
v___x_806_ = lean_uint64_to_usize(v___x_805_);
v___x_807_ = lean_usize_of_nat(v___x_797_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_sub(v___x_807_, v___x_808_);
v___x_810_ = lean_usize_land(v___x_806_, v___x_809_);
v___x_811_ = lean_array_uget_borrowed(v_buckets_796_, v___x_810_);
v___x_812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_795_, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_m_815_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_array_get_size(v_keys_818_);
v___x_822_ = lean_nat_dec_lt(v_i_819_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec(v_i_819_);
return v___x_822_;
}
else
{
lean_object* v_k_x27_823_; uint8_t v___x_824_; 
v_k_x27_823_ = lean_array_fget_borrowed(v_keys_818_, v_i_819_);
v___x_824_ = l_Lean_instBEqExtraModUse_beq(v_k_820_, v_k_x27_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_i_819_, v___x_825_);
lean_dec(v_i_819_);
v_i_819_ = v___x_826_;
goto _start;
}
else
{
lean_dec(v_i_819_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_828_, lean_object* v_i_829_, lean_object* v_k_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_828_, v_i_829_, v_k_830_);
lean_dec_ref(v_k_830_);
lean_dec_ref(v_keys_828_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; 
v___x_833_ = ((size_t)5ULL);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_shift_left(v___x_834_, v___x_833_);
return v___x_835_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; 
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__0);
v___x_838_ = lean_usize_sub(v___x_837_, v___x_836_);
return v___x_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_839_, size_t v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v_es_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v_j_847_; lean_object* v___x_848_; 
v_es_842_ = lean_ctor_get(v_x_839_, 0);
v___x_843_ = lean_box(2);
v___x_844_ = ((size_t)5ULL);
v___x_845_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___closed__1);
v___x_846_ = lean_usize_land(v_x_840_, v___x_845_);
v_j_847_ = lean_usize_to_nat(v___x_846_);
v___x_848_ = lean_array_get_borrowed(v___x_843_, v_es_842_, v_j_847_);
lean_dec(v_j_847_);
switch(lean_obj_tag(v___x_848_))
{
case 0:
{
lean_object* v_key_849_; uint8_t v___x_850_; 
v_key_849_ = lean_ctor_get(v___x_848_, 0);
v___x_850_ = l_Lean_instBEqExtraModUse_beq(v_x_841_, v_key_849_);
return v___x_850_;
}
case 1:
{
lean_object* v_node_851_; size_t v___x_852_; 
v_node_851_ = lean_ctor_get(v___x_848_, 0);
v___x_852_ = lean_usize_shift_right(v_x_840_, v___x_844_);
v_x_839_ = v_node_851_;
v_x_840_ = v___x_852_;
goto _start;
}
default: 
{
uint8_t v___x_854_; 
v___x_854_ = 0;
return v___x_854_;
}
}
}
else
{
lean_object* v_ks_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_ks_855_ = lean_ctor_get(v_x_839_, 0);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_855_, v___x_856_, v_x_841_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
size_t v_x_281500__boxed_861_; uint8_t v_res_862_; lean_object* v_r_863_; 
v_x_281500__boxed_861_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_res_862_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_858_, v_x_281500__boxed_861_, v_x_860_);
lean_dec_ref(v_x_860_);
lean_dec_ref(v_x_858_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
uint64_t v___x_866_; size_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = l_Lean_instHashableExtraModUse_hash(v_x_865_);
v___x_867_ = lean_uint64_to_usize(v___x_866_);
v___x_868_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_864_, v___x_867_, v_x_865_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_869_, v_x_870_);
lean_dec_ref(v_x_870_);
lean_dec_ref(v_x_869_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_876_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_877_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_884_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_ctor_set(v___x_884_, 3, v___x_883_);
lean_ctor_set(v___x_884_, 4, v___x_883_);
lean_ctor_set(v___x_884_, 5, v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_cls_896_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_897_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_898_ = l_Lean_Name_append(v___x_897_, v_cls_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_909_, uint8_t v_isMeta_910_, lean_object* v_hint_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_env_920_; uint8_t v_isExporting_921_; lean_object* v___x_922_; lean_object* v_env_923_; lean_object* v___x_924_; lean_object* v_entry_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_919_ = lean_st_ref_get(v___y_917_);
v_env_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_ref(v_env_920_);
lean_dec(v___x_919_);
v_isExporting_921_ = lean_ctor_get_uint8(v_env_920_, sizeof(void*)*8);
lean_dec_ref(v_env_920_);
v___x_922_ = lean_st_ref_get(v___y_917_);
v_env_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_env_923_);
lean_dec(v___x_922_);
v___x_924_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_909_);
v_entry_925_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_925_, 0, v_mod_909_);
lean_ctor_set_uint8(v_entry_925_, sizeof(void*)*1, v_isExporting_921_);
lean_ctor_set_uint8(v_entry_925_, sizeof(void*)*1 + 1, v_isMeta_910_);
v___x_926_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_927_ = lean_box(1);
v___x_928_ = lean_box(0);
v___x_971_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_924_, v___x_926_, v_env_923_, v___x_927_, v___x_928_);
v___x_972_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_971_, v_entry_925_);
lean_dec(v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v_options_973_; uint8_t v_hasTrace_974_; 
v_options_973_ = lean_ctor_get(v___y_916_, 2);
v_hasTrace_974_ = lean_ctor_get_uint8(v_options_973_, sizeof(void*)*1);
if (v_hasTrace_974_ == 0)
{
lean_dec(v_hint_911_);
lean_dec(v_mod_909_);
v___y_930_ = v___y_915_;
v___y_931_ = v___y_917_;
goto v___jp_929_;
}
else
{
lean_object* v_inheritedTraceOptions_975_; lean_object* v_cls_976_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_inheritedTraceOptions_975_ = lean_ctor_get(v___y_916_, 13);
v_cls_976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_996_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_997_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_975_, v_options_973_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec(v_hint_911_);
lean_dec(v_mod_909_);
v___y_930_ = v___y_915_;
v___y_931_ = v___y_917_;
goto v___jp_929_;
}
else
{
lean_object* v___x_998_; lean_object* v___y_1000_; 
v___x_998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_921_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_1000_ = v___x_1007_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_1000_ = v___x_1008_;
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref(v___y_1000_);
v___x_1001_ = l_Lean_stringToMessageData(v___y_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
if (v_isMeta_910_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_983_ = v___x_1004_;
v___y_984_ = v___x_1005_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_983_ = v___x_1004_;
v___y_984_ = v___x_1006_;
goto v___jp_982_;
}
}
}
v___jp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_978_);
lean_ctor_set(v___x_980_, 1, v___y_979_);
v___x_981_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_976_, v___x_980_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_dec_ref(v___x_981_);
v___y_930_ = v___y_915_;
v___y_931_ = v___y_917_;
goto v___jp_929_;
}
else
{
lean_dec_ref(v_entry_925_);
return v___x_981_;
}
}
v___jp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
lean_inc_ref(v___y_984_);
v___x_985_ = l_Lean_stringToMessageData(v___y_984_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___y_983_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_MessageData_ofName(v_mod_909_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Name_isAnonymous(v_hint_911_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_993_ = l_Lean_MessageData_ofName(v_hint_911_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___y_978_ = v___x_990_;
v___y_979_ = v___x_994_;
goto v___jp_977_;
}
else
{
lean_object* v___x_995_; 
lean_dec(v_hint_911_);
v___x_995_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_978_ = v___x_990_;
v___y_979_ = v___x_995_;
goto v___jp_977_;
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v_entry_925_);
lean_dec(v_hint_911_);
lean_dec(v_mod_909_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
v___jp_929_:
{
lean_object* v___x_932_; lean_object* v_toEnvExtension_933_; lean_object* v_env_934_; lean_object* v_nextMacroScope_935_; lean_object* v_ngen_936_; lean_object* v_auxDeclNGen_937_; lean_object* v_traceState_938_; lean_object* v_messages_939_; lean_object* v_infoState_940_; lean_object* v_snapshotTasks_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_969_; 
v___x_932_ = lean_st_ref_take(v___y_931_);
v_toEnvExtension_933_ = lean_ctor_get(v___x_926_, 0);
v_env_934_ = lean_ctor_get(v___x_932_, 0);
v_nextMacroScope_935_ = lean_ctor_get(v___x_932_, 1);
v_ngen_936_ = lean_ctor_get(v___x_932_, 2);
v_auxDeclNGen_937_ = lean_ctor_get(v___x_932_, 3);
v_traceState_938_ = lean_ctor_get(v___x_932_, 4);
v_messages_939_ = lean_ctor_get(v___x_932_, 6);
v_infoState_940_ = lean_ctor_get(v___x_932_, 7);
v_snapshotTasks_941_ = lean_ctor_get(v___x_932_, 8);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v___x_932_, 5);
lean_dec(v_unused_970_);
v___x_943_ = v___x_932_;
v_isShared_944_ = v_isSharedCheck_969_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snapshotTasks_941_);
lean_inc(v_infoState_940_);
lean_inc(v_messages_939_);
lean_inc(v_traceState_938_);
lean_inc(v_auxDeclNGen_937_);
lean_inc(v_ngen_936_);
lean_inc(v_nextMacroScope_935_);
lean_inc(v_env_934_);
lean_dec(v___x_932_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_969_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_asyncMode_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v_asyncMode_945_ = lean_ctor_get(v_toEnvExtension_933_, 2);
v___x_946_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_926_, v_env_934_, v_entry_925_, v_asyncMode_945_, v___x_928_);
v___x_947_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 5, v___x_947_);
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_nextMacroScope_935_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_ngen_936_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_auxDeclNGen_937_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_traceState_938_);
lean_ctor_set(v_reuseFailAlloc_968_, 5, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_968_, 6, v_messages_939_);
lean_ctor_set(v_reuseFailAlloc_968_, 7, v_infoState_940_);
lean_ctor_set(v_reuseFailAlloc_968_, 8, v_snapshotTasks_941_);
v___x_949_ = v_reuseFailAlloc_968_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_mctx_952_; lean_object* v_zetaDeltaFVarIds_953_; lean_object* v_postponed_954_; lean_object* v_diag_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v___x_950_ = lean_st_ref_set(v___y_931_, v___x_949_);
v___x_951_ = lean_st_ref_take(v___y_930_);
v_mctx_952_ = lean_ctor_get(v___x_951_, 0);
v_zetaDeltaFVarIds_953_ = lean_ctor_get(v___x_951_, 2);
v_postponed_954_ = lean_ctor_get(v___x_951_, 3);
v_diag_955_ = lean_ctor_get(v___x_951_, 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_951_, 1);
lean_dec(v_unused_967_);
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_diag_955_);
lean_inc(v_postponed_954_);
lean_inc(v_zetaDeltaFVarIds_953_);
lean_inc(v_mctx_952_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mctx_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_zetaDeltaFVarIds_953_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_postponed_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_diag_955_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_st_ref_set(v___y_930_, v___x_961_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1011_, lean_object* v_isMeta_1012_, lean_object* v_hint_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v_isMeta_boxed_1021_; lean_object* v_res_1022_; 
v_isMeta_boxed_1021_ = lean_unbox(v_isMeta_1012_);
v_res_1022_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1011_, v_isMeta_boxed_1021_, v_hint_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1023_, lean_object* v_declName_1024_, lean_object* v_as_1025_, size_t v_sz_1026_, size_t v_i_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_lt(v_i_1027_, v_sz_1026_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec(v_declName_1024_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_b_1028_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v_modules_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v_toImport_1043_; lean_object* v_module_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1038_ = l_Lean_Environment_header(v___x_1023_);
v_modules_1039_ = lean_ctor_get(v___x_1038_, 3);
lean_inc_ref(v_modules_1039_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1041_ = lean_array_uget_borrowed(v_as_1025_, v_i_1027_);
v___x_1042_ = lean_array_get(v___x_1040_, v_modules_1039_, v_a_1041_);
lean_dec_ref(v_modules_1039_);
v_toImport_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_ref(v_toImport_1043_);
lean_dec(v___x_1042_);
v_module_1044_ = lean_ctor_get(v_toImport_1043_, 0);
lean_inc(v_module_1044_);
lean_dec_ref(v_toImport_1043_);
v___x_1045_ = 0;
lean_inc(v_declName_1024_);
v___x_1046_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1044_, v___x_1045_, v_declName_1024_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; 
lean_dec_ref(v___x_1046_);
v___x_1047_ = lean_box(0);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1027_, v___x_1048_);
v_i_1027_ = v___x_1049_;
v_b_1028_ = v___x_1047_;
goto _start;
}
else
{
lean_dec(v_declName_1024_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1051_, lean_object* v_declName_1052_, lean_object* v_as_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
size_t v_sz_boxed_1064_; size_t v_i_boxed_1065_; lean_object* v_res_1066_; 
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1065_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1051_, v_declName_1052_, v_as_1053_, v_sz_boxed_1064_, v_i_boxed_1065_, v_b_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v_as_1053_);
lean_dec_ref(v___x_1051_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1070_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1071_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1070_, v___x_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1074_, uint8_t v_isMeta_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_env_1087_; lean_object* v___y_1089_; lean_object* v___x_1102_; 
v___x_1083_ = lean_st_ref_get(v___y_1081_);
v_env_1087_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1087_);
lean_dec(v___x_1083_);
v___x_1102_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1087_, v_declName_1074_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec_ref(v_env_1087_);
lean_dec(v_declName_1074_);
goto v___jp_1084_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1104_; lean_object* v_modules_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = l_Lean_Environment_header(v_env_1087_);
v_modules_1105_ = lean_ctor_get(v___x_1104_, 3);
lean_inc_ref(v_modules_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_array_get_size(v_modules_1105_);
v___x_1107_ = lean_nat_dec_lt(v_val_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v_modules_1105_);
lean_dec(v_val_1103_);
lean_dec_ref(v_env_1087_);
lean_dec(v_declName_1074_);
goto v___jp_1084_;
}
else
{
lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___y_1113_; 
v___x_1108_ = lean_st_ref_get(v___y_1081_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1110_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1111_ = lean_array_fget(v_modules_1105_, v_val_1103_);
lean_dec(v_val_1103_);
lean_dec_ref(v_modules_1105_);
if (v_isMeta_1075_ == 0)
{
lean_dec_ref(v_env_1109_);
v___y_1113_ = v_isMeta_1075_;
goto v___jp_1112_;
}
else
{
uint8_t v___x_1124_; 
lean_inc(v_declName_1074_);
v___x_1124_ = l_Lean_isMarkedMeta(v_env_1109_, v_declName_1074_);
if (v___x_1124_ == 0)
{
v___y_1113_ = v_isMeta_1075_;
goto v___jp_1112_;
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
v___y_1113_ = v___x_1125_;
goto v___jp_1112_;
}
}
v___jp_1112_:
{
lean_object* v_toImport_1114_; lean_object* v_module_1115_; lean_object* v___x_1116_; 
v_toImport_1114_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_toImport_1114_);
lean_dec(v___x_1111_);
v_module_1115_ = lean_ctor_get(v_toImport_1114_, 0);
lean_inc(v_module_1115_);
lean_dec_ref(v_toImport_1114_);
lean_inc(v_declName_1074_);
v___x_1116_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1115_, v___y_1113_, v_declName_1074_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___x_1116_);
v___x_1117_ = l_Lean_indirectModUseExt;
v___x_1118_ = lean_box(1);
v___x_1119_ = lean_box(0);
lean_inc_ref(v_env_1087_);
v___x_1120_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1110_, v___x_1117_, v_env_1087_, v___x_1118_, v___x_1119_);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1120_, v_declName_1074_);
lean_dec(v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1089_ = v___x_1122_;
goto v___jp_1088_;
}
else
{
lean_object* v_val_1123_; 
v_val_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1121_);
v___y_1089_ = v_val_1123_;
goto v___jp_1088_;
}
}
else
{
lean_dec_ref(v_env_1087_);
lean_dec(v_declName_1074_);
return v___x_1116_;
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; size_t v_sz_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1090_ = lean_box(0);
v_sz_1091_ = lean_array_size(v___y_1089_);
v___x_1092_ = ((size_t)0ULL);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1087_, v_declName_1074_, v___y_1089_, v_sz_1091_, v___x_1092_, v___x_1090_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec_ref(v___y_1089_);
lean_dec_ref(v_env_1087_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1090_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1090_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1126_, lean_object* v_isMeta_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
uint8_t v_isMeta_boxed_1135_; lean_object* v_res_1136_; 
v_isMeta_boxed_1135_ = lean_unbox(v_isMeta_1127_);
v_res_1136_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1126_, v_isMeta_boxed_1135_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
if (lean_obj_tag(v_as_x27_1137_) == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_b_1138_);
return v___x_1146_;
}
else
{
lean_object* v_head_1147_; lean_object* v_tail_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v_head_1147_ = lean_ctor_get(v_as_x27_1137_, 0);
v_tail_1148_ = lean_ctor_get(v_as_x27_1137_, 1);
v___x_1149_ = 1;
lean_inc(v_head_1147_);
v___x_1150_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1147_, v___x_1149_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; 
lean_dec_ref(v___x_1150_);
v___x_1151_ = lean_box(0);
v_as_x27_1137_ = v_tail_1148_;
v_b_1138_ = v___x_1151_;
goto _start;
}
else
{
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1153_, v_b_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v_as_x27_1153_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1163_, lean_object* v_currNamespace_1164_, lean_object* v_openDecls_1165_, lean_object* v_n_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = l_Lean_ResolveName_resolveNamespace(v_env_1163_, v_currNamespace_1164_, v_openDecls_1165_, v_n_1166_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1171_, lean_object* v_currNamespace_1172_, lean_object* v_openDecls_1173_, lean_object* v_n_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1171_, v_currNamespace_1172_, v_openDecls_1173_, v_n_1174_, v___y_1175_, v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_currNamespace_1178_);
lean_ctor_set(v___x_1181_, 1, v___y_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1186_, lean_object* v_options_1187_, lean_object* v_currNamespace_1188_, lean_object* v_openDecls_1189_, lean_object* v_n_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_ResolveName_resolveGlobalName(v_env_1186_, v_options_1187_, v_currNamespace_1188_, v_openDecls_1189_, v_n_1190_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1195_, lean_object* v_options_1196_, lean_object* v_currNamespace_1197_, lean_object* v_openDecls_1198_, lean_object* v_n_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1195_, v_options_1196_, v_currNamespace_1197_, v_openDecls_1198_, v_n_1199_, v___y_1200_, v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_options_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_env_1213_; lean_object* v_options_1214_; lean_object* v_currRecDepth_1215_; lean_object* v_maxRecDepth_1216_; lean_object* v_ref_1217_; lean_object* v_currNamespace_1218_; lean_object* v_openDecls_1219_; lean_object* v_quotContext_1220_; lean_object* v_currMacroScope_1221_; lean_object* v___x_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v_methods_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1212_ = lean_st_ref_get(v___y_1210_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref_n(v_env_1213_, 4);
lean_dec(v___x_1212_);
v_options_1214_ = lean_ctor_get(v___y_1209_, 2);
v_currRecDepth_1215_ = lean_ctor_get(v___y_1209_, 3);
v_maxRecDepth_1216_ = lean_ctor_get(v___y_1209_, 4);
v_ref_1217_ = lean_ctor_get(v___y_1209_, 5);
v_currNamespace_1218_ = lean_ctor_get(v___y_1209_, 6);
v_openDecls_1219_ = lean_ctor_get(v___y_1209_, 7);
v_quotContext_1220_ = lean_ctor_get(v___y_1209_, 10);
v_currMacroScope_1221_ = lean_ctor_get(v___y_1209_, 11);
v___x_1222_ = lean_st_ref_get(v___y_1210_);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_nextMacroScope_1223_);
lean_dec(v___x_1222_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1224_, 0, v_env_1213_);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1225_, 0, v_env_1213_);
lean_inc_n(v_openDecls_1219_, 2);
lean_inc_n(v_currNamespace_1218_, 3);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1226_, 0, v_env_1213_);
lean_closure_set(v___f_1226_, 1, v_currNamespace_1218_);
lean_closure_set(v___f_1226_, 2, v_openDecls_1219_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1227_, 0, v_currNamespace_1218_);
lean_inc_ref(v_options_1214_);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1228_, 0, v_env_1213_);
lean_closure_set(v___f_1228_, 1, v_options_1214_);
lean_closure_set(v___f_1228_, 2, v_currNamespace_1218_);
lean_closure_set(v___f_1228_, 3, v_openDecls_1219_);
v_methods_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1229_, 0, v___f_1224_);
lean_ctor_set(v_methods_1229_, 1, v___f_1227_);
lean_ctor_set(v_methods_1229_, 2, v___f_1225_);
lean_ctor_set(v_methods_1229_, 3, v___f_1226_);
lean_ctor_set(v_methods_1229_, 4, v___f_1228_);
lean_inc(v_ref_1217_);
lean_inc(v_maxRecDepth_1216_);
lean_inc(v_currRecDepth_1215_);
lean_inc(v_currMacroScope_1221_);
lean_inc(v_quotContext_1220_);
v___x_1230_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1230_, 0, v_methods_1229_);
lean_ctor_set(v___x_1230_, 1, v_quotContext_1220_);
lean_ctor_set(v___x_1230_, 2, v_currMacroScope_1221_);
lean_ctor_set(v___x_1230_, 3, v_currRecDepth_1215_);
lean_ctor_set(v___x_1230_, 4, v_maxRecDepth_1216_);
lean_ctor_set(v___x_1230_, 5, v_ref_1217_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1232_, 0, v_nextMacroScope_1223_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
v___x_1233_ = lean_apply_2(v_x_1204_, v___x_1230_, v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v_macroScope_1236_; lean_object* v_traceMsgs_1237_; lean_object* v_expandedMacroDecls_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 1);
lean_inc(v_a_1234_);
v_a_1235_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1233_);
v_macroScope_1236_ = lean_ctor_get(v_a_1234_, 0);
lean_inc(v_macroScope_1236_);
v_traceMsgs_1237_ = lean_ctor_get(v_a_1234_, 1);
lean_inc(v_traceMsgs_1237_);
v_expandedMacroDecls_1238_ = lean_ctor_get(v_a_1234_, 2);
lean_inc(v_expandedMacroDecls_1238_);
lean_dec(v_a_1234_);
v___x_1239_ = lean_box(0);
v___x_1240_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1238_, v___x_1239_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v_expandedMacroDecls_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; lean_object* v_env_1242_; lean_object* v_ngen_1243_; lean_object* v_auxDeclNGen_1244_; lean_object* v_traceState_1245_; lean_object* v_cache_1246_; lean_object* v_messages_1247_; lean_object* v_infoState_1248_; lean_object* v_snapshotTasks_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v___x_1240_);
v___x_1241_ = lean_st_ref_take(v___y_1210_);
v_env_1242_ = lean_ctor_get(v___x_1241_, 0);
v_ngen_1243_ = lean_ctor_get(v___x_1241_, 2);
v_auxDeclNGen_1244_ = lean_ctor_get(v___x_1241_, 3);
v_traceState_1245_ = lean_ctor_get(v___x_1241_, 4);
v_cache_1246_ = lean_ctor_get(v___x_1241_, 5);
v_messages_1247_ = lean_ctor_get(v___x_1241_, 6);
v_infoState_1248_ = lean_ctor_get(v___x_1241_, 7);
v_snapshotTasks_1249_ = lean_ctor_get(v___x_1241_, 8);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1241_, 1);
lean_dec(v_unused_1276_);
v___x_1251_ = v___x_1241_;
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snapshotTasks_1249_);
lean_inc(v_infoState_1248_);
lean_inc(v_messages_1247_);
lean_inc(v_cache_1246_);
lean_inc(v_traceState_1245_);
lean_inc(v_auxDeclNGen_1244_);
lean_inc(v_ngen_1243_);
lean_inc(v_env_1242_);
lean_dec(v___x_1241_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_macroScope_1236_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_env_1242_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_macroScope_1236_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_ngen_1243_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_auxDeclNGen_1244_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_traceState_1245_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v_cache_1246_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_messages_1247_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_infoState_1248_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_snapshotTasks_1249_);
v___x_1254_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_st_ref_set(v___y_1210_, v___x_1254_);
v___x_1256_ = l_List_reverse___redArg(v_traceMsgs_1237_);
v___x_1257_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1256_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1265_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v_a_1235_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1235_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1235_);
v_a_1266_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_traceMsgs_1237_);
lean_dec(v_macroScope_1236_);
lean_dec(v_a_1235_);
v_a_1277_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1240_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1240_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; 
v_a_1285_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1285_);
lean_dec_ref(v___x_1233_);
if (lean_obj_tag(v_a_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_a_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_a_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_a_1286_);
v_a_1287_ = lean_ctor_get(v_a_1285_, 1);
lean_inc_ref(v_a_1287_);
lean_dec_ref(v_a_1285_);
v___x_1288_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1289_ = lean_string_dec_eq(v_a_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_a_1287_);
v___x_1291_ = l_Lean_MessageData_ofFormat(v___x_1290_);
v___x_1292_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1286_, v___x_1291_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v_a_1286_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v_a_1287_);
v___x_1293_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1286_);
return v___x_1293_;
}
}
else
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1307_, size_t v_i_1308_, lean_object* v_bs_1309_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_usize_dec_lt(v_i_1308_, v_sz_1307_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_bs_1309_);
return v___x_1311_;
}
else
{
lean_object* v_v_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_v_1312_ = lean_array_uget(v_bs_1309_, v_i_1308_);
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1312_);
v___x_1314_ = l_Lean_Syntax_isOfKind(v_v_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_v_1312_);
lean_dec_ref(v_bs_1309_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = l_Lean_Syntax_getArg(v_v_1312_, v___x_1316_);
v___x_1318_ = l_Lean_Syntax_isOfKind(v___x_1317_, v___x_1313_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_v_1312_);
lean_dec_ref(v_bs_1309_);
v___x_1319_ = lean_box(0);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v_bs_x27_1321_; lean_object* v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1320_ = lean_unsigned_to_nat(3u);
v_bs_x27_1321_ = lean_array_uset(v_bs_1309_, v_i_1308_, v___x_1316_);
v___x_1322_ = l_Lean_Syntax_getArg(v_v_1312_, v___x_1320_);
lean_dec(v_v_1312_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1308_, v___x_1323_);
v___x_1325_ = lean_array_uset(v_bs_x27_1321_, v_i_1308_, v___x_1322_);
v_i_1308_ = v___x_1324_;
v_bs_1309_ = v___x_1325_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_bs_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1330_, v_i_boxed_1331_, v_bs_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t v_sz_1345_, size_t v_i_1346_, lean_object* v_bs_1347_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_usize_dec_lt(v_i_1346_, v_sz_1345_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_bs_1347_);
return v___x_1349_;
}
else
{
lean_object* v_v_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_v_1350_ = lean_array_uget(v_bs_1347_, v_i_1346_);
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1350_);
v___x_1352_ = l_Lean_Syntax_isOfKind(v_v_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v_v_1350_);
lean_dec_ref(v_bs_1347_);
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = l_Lean_Syntax_getArg(v_v_1350_, v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1357_ = l_Lean_Syntax_isOfKind(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_v_1350_);
lean_dec_ref(v_bs_1347_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1359_ = lean_unsigned_to_nat(3u);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1347_, v_i_1346_, v___x_1360_);
v___x_1362_ = l_Lean_Syntax_getArg(v_v_1350_, v___x_1359_);
lean_dec(v_v_1350_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1346_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1361_, v_i_1346_, v___x_1362_);
v_i_1346_ = v___x_1364_;
v_bs_1347_ = v___x_1365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v_sz_1367_, lean_object* v_i_1368_, lean_object* v_bs_1369_){
_start:
{
size_t v_sz_boxed_1370_; size_t v_i_boxed_1371_; lean_object* v_res_1372_; 
v_sz_boxed_1370_ = lean_unbox_usize(v_sz_1367_);
lean_dec(v_sz_1367_);
v_i_boxed_1371_ = lean_unbox_usize(v_i_1368_);
lean_dec(v_i_1368_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_boxed_1370_, v_i_boxed_1371_, v_bs_1369_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_bs_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_bs_1381_);
return v___x_1383_;
}
else
{
lean_object* v_v_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_v_1384_ = lean_array_uget(v_bs_1381_, v_i_1380_);
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1384_);
v___x_1386_ = l_Lean_Syntax_isOfKind(v_v_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec(v_v_1384_);
lean_dec_ref(v_bs_1381_);
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v_bs_x27_1389_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
v_bs_x27_1389_ = lean_array_uset(v_bs_1381_, v_i_1380_, v___x_1388_);
v___x_1396_ = l_Lean_Syntax_getArg(v_v_1384_, v___x_1388_);
lean_dec(v_v_1384_);
v___x_1397_ = l_Lean_Syntax_isNone(v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(2u);
v___x_1399_ = l_Lean_Syntax_matchesNull(v___x_1396_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_bs_x27_1389_);
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
else
{
goto v___jp_1390_;
}
}
else
{
lean_dec(v___x_1396_);
goto v___jp_1390_;
}
v___jp_1390_:
{
lean_object* v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1380_, v___x_1392_);
v___x_1394_ = lean_array_uset(v_bs_x27_1389_, v_i_1380_, v___x_1391_);
v_i_1380_ = v___x_1393_;
v_bs_1381_ = v___x_1394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1401_, lean_object* v_i_1402_, lean_object* v_bs_1403_){
_start:
{
size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1401_);
lean_dec(v_sz_1401_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1404_, v_i_boxed_1405_, v_bs_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1407_, size_t v_i_1408_, lean_object* v_bs_1409_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_lt(v_i_1408_, v_sz_1407_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_bs_1409_);
return v___x_1411_;
}
else
{
lean_object* v_v_1412_; lean_object* v___x_1413_; lean_object* v_bs_x27_1414_; size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v_v_1412_ = lean_array_uget(v_bs_1409_, v_i_1408_);
v___x_1413_ = lean_unsigned_to_nat(0u);
v_bs_x27_1414_ = lean_array_uset(v_bs_1409_, v_i_1408_, v___x_1413_);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1408_, v___x_1415_);
v___x_1417_ = lean_array_uset(v_bs_x27_1414_, v_i_1408_, v_v_1412_);
v_i_1408_ = v___x_1416_;
v_bs_1409_ = v___x_1417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_){
_start:
{
size_t v_sz_boxed_1422_; size_t v_i_boxed_1423_; lean_object* v_res_1424_; 
v_sz_boxed_1422_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1423_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1422_, v_i_boxed_1423_, v_bs_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1426_, v___y_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1430_, v_x_1431_, v___y_1432_, v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_x_1431_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1438_, lean_object* v_as_x27_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
if (lean_obj_tag(v_as_x27_1439_) == 0)
{
lean_object* v___x_1448_; 
lean_dec(v_stx_1438_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1440_);
return v___x_1448_;
}
else
{
lean_object* v_head_1449_; lean_object* v_tail_1450_; lean_object* v_value_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_b_1440_);
v_head_1449_ = lean_ctor_get(v_as_x27_1439_, 0);
v_tail_1450_ = lean_ctor_get(v_as_x27_1439_, 1);
v_value_1451_ = lean_ctor_get(v_head_1449_, 1);
v___x_1452_ = lean_box(0);
lean_inc(v_value_1451_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v_stx_1438_);
v___x_1453_ = lean_apply_8(v_value_1451_, v_stx_1438_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, lean_box(0));
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_stx_1438_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_a_1454_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1452_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1486_; 
v_a_1464_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1466_ = v___x_1453_;
v_isShared_1467_ = v_isSharedCheck_1486_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1453_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1486_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___y_1471_; uint8_t v___x_1484_; 
v___x_1468_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1469_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1484_ = l_Lean_Exception_isInterrupt(v_a_1464_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
lean_inc(v_a_1464_);
v___x_1485_ = l_Lean_Exception_isRuntime(v_a_1464_);
v___y_1471_ = v___x_1485_;
goto v___jp_1470_;
}
else
{
v___y_1471_ = v___x_1484_;
goto v___jp_1470_;
}
v___jp_1470_:
{
if (v___y_1471_ == 0)
{
if (lean_obj_tag(v_a_1464_) == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_stx_1438_);
if (v_isShared_1467_ == 0)
{
v___x_1473_ = v___x_1466_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1464_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v_id_1475_; uint8_t v___x_1476_; 
v_id_1475_ = lean_ctor_get(v_a_1464_, 0);
v___x_1476_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1469_, v_id_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1478_; 
lean_dec(v_stx_1438_);
if (v_isShared_1467_ == 0)
{
v___x_1478_ = v___x_1466_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1464_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
else
{
lean_dec_ref(v_a_1464_);
lean_del_object(v___x_1466_);
v_as_x27_1439_ = v_tail_1450_;
v_b_1440_ = v___x_1468_;
goto _start;
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec(v_stx_1438_);
if (v_isShared_1467_ == 0)
{
v___x_1482_ = v___x_1466_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1464_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1487_, lean_object* v_as_x27_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1487_, v_as_x27_1488_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_as_x27_1488_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1500_, lean_object* v_rhs_x3f_1501_, lean_object* v_otherwise_x3f_1502_, lean_object* v_body_x3f_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___y_1512_; uint8_t v___y_1513_; uint8_t v___y_1514_; uint8_t v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v_body_1523_; lean_object* v___y_1544_; lean_object* v_otherwise_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_rhs_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; 
if (lean_obj_tag(v_rhs_x3f_1501_) == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1557_ = v___x_1568_;
v___y_1558_ = v_a_1504_;
v___y_1559_ = v_a_1505_;
v___y_1560_ = v_a_1506_;
v___y_1561_ = v_a_1507_;
v___y_1562_ = v_a_1508_;
v___y_1563_ = v_a_1509_;
goto v___jp_1556_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1570_; 
v_val_1569_ = lean_ctor_get(v_rhs_x3f_1501_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v_rhs_x3f_1501_);
v___x_1570_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1569_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
v_rhs_1557_ = v_a_1571_;
v___y_1558_ = v_a_1504_;
v___y_1559_ = v_a_1505_;
v___y_1560_ = v_a_1506_;
v___y_1561_ = v_a_1507_;
v___y_1562_ = v_a_1508_;
v___y_1563_ = v_a_1509_;
goto v___jp_1556_;
}
else
{
lean_dec(v_body_x3f_1503_);
lean_dec(v_otherwise_x3f_1502_);
lean_dec_ref(v_reassigned_1500_);
return v___x_1570_;
}
}
v___jp_1511_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1518_, 0, v___y_1512_);
lean_ctor_set(v___x_1518_, 1, v___y_1517_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*2, v___y_1513_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*2 + 1, v___y_1515_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*2 + 2, v___y_1514_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*2 + 3, v___y_1516_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
v___jp_1520_:
{
lean_object* v___x_1524_; lean_object* v_info_1525_; uint8_t v_breaks_1526_; uint8_t v_continues_1527_; uint8_t v_returnsEarly_1528_; lean_object* v_numRegularExits_1529_; uint8_t v_noFallthrough_1530_; lean_object* v_reassigns_1531_; size_t v_sz_1532_; size_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1524_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1523_, v___y_1521_);
v_info_1525_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1522_, v___x_1524_);
v_breaks_1526_ = lean_ctor_get_uint8(v_info_1525_, sizeof(void*)*2);
v_continues_1527_ = lean_ctor_get_uint8(v_info_1525_, sizeof(void*)*2 + 1);
v_returnsEarly_1528_ = lean_ctor_get_uint8(v_info_1525_, sizeof(void*)*2 + 2);
v_numRegularExits_1529_ = lean_ctor_get(v_info_1525_, 0);
lean_inc(v_numRegularExits_1529_);
v_noFallthrough_1530_ = lean_ctor_get_uint8(v_info_1525_, sizeof(void*)*2 + 3);
v_reassigns_1531_ = lean_ctor_get(v_info_1525_, 1);
lean_inc(v_reassigns_1531_);
lean_dec_ref(v_info_1525_);
v_sz_1532_ = lean_array_size(v_reassigned_1500_);
v___x_1533_ = ((size_t)0ULL);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1532_, v___x_1533_, v_reassigned_1500_);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_array_get_size(v___x_1534_);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec_ref(v___x_1534_);
v___y_1512_ = v_numRegularExits_1529_;
v___y_1513_ = v_breaks_1526_;
v___y_1514_ = v_returnsEarly_1528_;
v___y_1515_ = v_continues_1527_;
v___y_1516_ = v_noFallthrough_1530_;
v___y_1517_ = v_reassigns_1531_;
goto v___jp_1511_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_le(v___x_1536_, v___x_1536_);
if (v___x_1538_ == 0)
{
if (v___x_1537_ == 0)
{
lean_dec_ref(v___x_1534_);
v___y_1512_ = v_numRegularExits_1529_;
v___y_1513_ = v_breaks_1526_;
v___y_1514_ = v_returnsEarly_1528_;
v___y_1515_ = v_continues_1527_;
v___y_1516_ = v_noFallthrough_1530_;
v___y_1517_ = v_reassigns_1531_;
goto v___jp_1511_;
}
else
{
size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_usize_of_nat(v___x_1536_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1534_, v___x_1533_, v___x_1539_, v_reassigns_1531_);
lean_dec_ref(v___x_1534_);
v___y_1512_ = v_numRegularExits_1529_;
v___y_1513_ = v_breaks_1526_;
v___y_1514_ = v_returnsEarly_1528_;
v___y_1515_ = v_continues_1527_;
v___y_1516_ = v_noFallthrough_1530_;
v___y_1517_ = v___x_1540_;
goto v___jp_1511_;
}
}
else
{
size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_usize_of_nat(v___x_1536_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1534_, v___x_1533_, v___x_1541_, v_reassigns_1531_);
lean_dec_ref(v___x_1534_);
v___y_1512_ = v_numRegularExits_1529_;
v___y_1513_ = v_breaks_1526_;
v___y_1514_ = v_returnsEarly_1528_;
v___y_1515_ = v_continues_1527_;
v___y_1516_ = v_noFallthrough_1530_;
v___y_1517_ = v___x_1542_;
goto v___jp_1511_;
}
}
}
v___jp_1543_:
{
if (lean_obj_tag(v_body_x3f_1503_) == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1521_ = v_otherwise_1545_;
v___y_1522_ = v___y_1544_;
v_body_1523_ = v___x_1552_;
goto v___jp_1520_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_body_x3f_1503_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_body_x3f_1503_);
v___x_1554_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1553_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___y_1521_ = v_otherwise_1545_;
v___y_1522_ = v___y_1544_;
v_body_1523_ = v_a_1555_;
goto v___jp_1520_;
}
else
{
lean_dec_ref(v_otherwise_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_reassigned_1500_);
return v___x_1554_;
}
}
}
v___jp_1556_:
{
if (lean_obj_tag(v_otherwise_x3f_1502_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1544_ = v_rhs_1557_;
v_otherwise_1545_ = v___x_1564_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
v___y_1548_ = v___y_1560_;
v___y_1549_ = v___y_1561_;
v___y_1550_ = v___y_1562_;
v___y_1551_ = v___y_1563_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1566_; 
v_val_1565_ = lean_ctor_get(v_otherwise_x3f_1502_, 0);
lean_inc(v_val_1565_);
lean_dec_ref(v_otherwise_x3f_1502_);
v___x_1566_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1565_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___y_1544_ = v_rhs_1557_;
v_otherwise_1545_ = v_a_1567_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1559_;
v___y_1548_ = v___y_1560_;
v___y_1549_ = v___y_1561_;
v___y_1550_ = v___y_1562_;
v___y_1551_ = v___y_1563_;
goto v___jp_1543_;
}
else
{
lean_dec_ref(v_rhs_1557_);
lean_dec(v_body_x3f_1503_);
lean_dec_ref(v_reassigned_1500_);
return v___x_1566_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1674_, lean_object* v_decl_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v_reassigns_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1675_);
v___x_1712_ = l_Lean_Syntax_isOfKind(v_decl_1675_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1675_);
v___x_1714_ = l_Lean_Syntax_isOfKind(v_decl_1675_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1716_ = lean_box(0);
v___x_1717_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1716_, v___x_1714_);
v___x_1718_ = l_Std_Format_defWidth;
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = l_Std_Format_pretty(v___x_1717_, v___x_1718_, v___x_1719_, v___x_1719_);
v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
v___x_1722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1715_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1722_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v_pattern_1725_; lean_object* v___y_1727_; lean_object* v_otherwise_x3f_1728_; lean_object* v_body_x3f_x3f_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v_body_x3f_x3f_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___x_1759_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v_pattern_1725_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1724_);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1798_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1759_);
v___x_1799_ = l_Lean_Syntax_isNone(v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
lean_inc(v___x_1798_);
v___x_1800_ = l_Lean_Syntax_matchesNull(v___x_1798_, v___x_1759_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1798_);
lean_dec(v_pattern_1725_);
v___x_1801_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1802_ = lean_box(0);
v___x_1803_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1802_, v___x_1800_);
v___x_1804_ = l_Std_Format_defWidth;
v___x_1805_ = l_Std_Format_pretty(v___x_1803_, v___x_1804_, v___x_1724_, v___x_1724_);
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1801_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1807_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_Syntax_getArg(v___x_1798_, v___x_1724_);
lean_dec(v___x_1798_);
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1811_ = l_Lean_Syntax_isOfKind(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_pattern_1725_);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1813_ = lean_box(0);
v___x_1814_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1813_, v___x_1811_);
v___x_1815_ = l_Std_Format_defWidth;
v___x_1816_ = l_Std_Format_pretty(v___x_1814_, v___x_1815_, v___x_1724_, v___x_1724_);
v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1812_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1818_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1819_;
}
else
{
v___y_1761_ = v_a_1676_;
v___y_1762_ = v_a_1677_;
v___y_1763_ = v_a_1678_;
v___y_1764_ = v_a_1679_;
v___y_1765_ = v_a_1680_;
v___y_1766_ = v_a_1681_;
goto v___jp_1760_;
}
}
}
else
{
lean_dec(v___x_1798_);
v___y_1761_ = v_a_1676_;
v___y_1762_ = v_a_1677_;
v___y_1763_ = v_a_1678_;
v___y_1764_ = v_a_1679_;
v___y_1765_ = v_a_1680_;
v___y_1766_ = v_a_1681_;
goto v___jp_1760_;
}
v___jp_1726_:
{
if (v_reassignment_1674_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v_pattern_1725_);
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1696_ = v_otherwise_x3f_1728_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v_body_x3f_x3f_1729_;
v_reassigns_1699_ = v___x_1736_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1732_;
v___y_1703_ = v___y_1733_;
v___y_1704_ = v___y_1734_;
v___y_1705_ = v___y_1735_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1725_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v___y_1696_ = v_otherwise_x3f_1728_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v_body_x3f_x3f_1729_;
v_reassigns_1699_ = v_a_1738_;
v___y_1700_ = v___y_1730_;
v___y_1701_ = v___y_1731_;
v___y_1702_ = v___y_1732_;
v___y_1703_ = v___y_1733_;
v___y_1704_ = v___y_1734_;
v___y_1705_ = v___y_1735_;
goto v___jp_1695_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_body_x3f_x3f_1729_);
lean_dec(v_otherwise_x3f_1728_);
lean_dec(v___y_1727_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
v___jp_1747_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1749_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_body_x3f_x3f_1750_);
v___y_1727_ = v___y_1748_;
v_otherwise_x3f_1728_ = v___x_1757_;
v_body_x3f_x3f_1729_ = v___x_1758_;
v___y_1730_ = v___y_1751_;
v___y_1731_ = v___y_1752_;
v___y_1732_ = v___y_1753_;
v___y_1733_ = v___y_1754_;
v___y_1734_ = v___y_1755_;
v___y_1735_ = v___y_1756_;
goto v___jp_1726_;
}
v___jp_1760_:
{
lean_object* v___x_1767_; lean_object* v_rhs_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1767_ = lean_unsigned_to_nat(3u);
v_rhs_1768_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1767_);
v___x_1769_ = lean_unsigned_to_nat(4u);
v___x_1770_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_isNone(v___x_1770_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; 
lean_inc(v___x_1770_);
v___x_1772_ = l_Lean_Syntax_matchesNull(v___x_1770_, v___x_1767_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v___x_1770_);
lean_dec(v_rhs_1768_);
lean_dec(v_pattern_1725_);
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1774_ = lean_box(0);
v___x_1775_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1774_, v___x_1772_);
v___x_1776_ = l_Std_Format_defWidth;
v___x_1777_ = l_Std_Format_pretty(v___x_1775_, v___x_1776_, v___x_1724_, v___x_1724_);
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1773_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1779_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v_otherwise_x3f_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1781_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1782_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1759_);
v___x_1783_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1781_);
lean_dec(v___x_1770_);
v___x_1784_ = l_Lean_Syntax_isNone(v___x_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc(v___x_1783_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1759_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v___x_1783_);
lean_dec(v_otherwise_x3f_1782_);
lean_dec(v_rhs_1768_);
lean_dec(v_pattern_1725_);
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1787_ = lean_box(0);
v___x_1788_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1787_, v___x_1785_);
v___x_1789_ = l_Std_Format_defWidth;
v___x_1790_ = l_Std_Format_pretty(v___x_1788_, v___x_1789_, v___x_1724_, v___x_1724_);
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1786_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1792_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1793_;
}
else
{
lean_object* v_body_x3f_x3f_1794_; lean_object* v___x_1795_; 
lean_dec(v_decl_1675_);
v_body_x3f_x3f_1794_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1724_);
lean_dec(v___x_1783_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_body_x3f_x3f_1794_);
v___y_1748_ = v_rhs_1768_;
v___y_1749_ = v_otherwise_x3f_1782_;
v_body_x3f_x3f_1750_ = v___x_1795_;
v___y_1751_ = v___y_1761_;
v___y_1752_ = v___y_1762_;
v___y_1753_ = v___y_1763_;
v___y_1754_ = v___y_1764_;
v___y_1755_ = v___y_1765_;
v___y_1756_ = v___y_1766_;
goto v___jp_1747_;
}
}
else
{
lean_object* v___x_1796_; 
lean_dec(v___x_1783_);
lean_dec(v_decl_1675_);
v___x_1796_ = lean_box(0);
v___y_1748_ = v_rhs_1768_;
v___y_1749_ = v_otherwise_x3f_1782_;
v_body_x3f_x3f_1750_ = v___x_1796_;
v___y_1751_ = v___y_1761_;
v___y_1752_ = v___y_1762_;
v___y_1753_ = v___y_1763_;
v___y_1754_ = v___y_1764_;
v___y_1755_ = v___y_1765_;
v___y_1756_ = v___y_1766_;
goto v___jp_1747_;
}
}
}
else
{
lean_object* v___x_1797_; 
lean_dec(v___x_1770_);
lean_dec(v_decl_1675_);
v___x_1797_ = lean_box(0);
v___y_1727_ = v_rhs_1768_;
v_otherwise_x3f_1728_ = v___x_1797_;
v_body_x3f_x3f_1729_ = v___x_1797_;
v___y_1730_ = v___y_1761_;
v___y_1731_ = v___y_1762_;
v___y_1732_ = v___y_1763_;
v___y_1733_ = v___y_1764_;
v___y_1734_ = v___y_1765_;
v___y_1735_ = v___y_1766_;
goto v___jp_1726_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v_x_1821_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1820_ = lean_unsigned_to_nat(0u);
v_x_1821_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1820_);
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1821_);
v___x_1836_ = l_Lean_Syntax_isOfKind(v_x_1821_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_x_1821_);
v___x_1837_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1838_ = lean_box(0);
v___x_1839_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1838_, v___x_1836_);
v___x_1840_ = l_Std_Format_defWidth;
v___x_1841_ = l_Std_Format_pretty(v___x_1839_, v___x_1840_, v___x_1820_, v___x_1820_);
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1837_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1843_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(1u);
v___x_1846_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1845_);
v___x_1847_ = l_Lean_Syntax_isNone(v___x_1846_);
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
lean_inc(v___x_1846_);
v___x_1848_ = l_Lean_Syntax_matchesNull(v___x_1846_, v___x_1845_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v___x_1846_);
lean_dec(v_x_1821_);
v___x_1849_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1850_, v___x_1848_);
v___x_1852_ = l_Std_Format_defWidth;
v___x_1853_ = l_Std_Format_pretty(v___x_1851_, v___x_1852_, v___x_1820_, v___x_1820_);
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1849_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1855_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1857_ = l_Lean_Syntax_getArg(v___x_1846_, v___x_1820_);
lean_dec(v___x_1846_);
v___x_1858_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1859_ = l_Lean_Syntax_isOfKind(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v_x_1821_);
v___x_1860_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1861_ = lean_box(0);
v___x_1862_ = l_Lean_Syntax_formatStx(v_decl_1675_, v___x_1861_, v___x_1859_);
v___x_1863_ = l_Std_Format_defWidth;
v___x_1864_ = l_Std_Format_pretty(v___x_1862_, v___x_1863_, v___x_1820_, v___x_1820_);
v___x_1865_ = l_Lean_stringToMessageData(v___x_1864_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1860_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1866_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1867_;
}
else
{
v___y_1823_ = v_a_1676_;
v___y_1824_ = v_a_1677_;
v___y_1825_ = v_a_1678_;
v___y_1826_ = v_a_1679_;
v___y_1827_ = v_a_1680_;
v___y_1828_ = v_a_1681_;
goto v___jp_1822_;
}
}
}
else
{
lean_dec(v___x_1846_);
v___y_1823_ = v_a_1676_;
v___y_1824_ = v_a_1677_;
v___y_1825_ = v_a_1678_;
v___y_1826_ = v_a_1679_;
v___y_1827_ = v_a_1680_;
v___y_1828_ = v_a_1681_;
goto v___jp_1822_;
}
}
v___jp_1822_:
{
lean_object* v___x_1829_; lean_object* v_rhs_1830_; 
v___x_1829_ = lean_unsigned_to_nat(3u);
v_rhs_1830_ = l_Lean_Syntax_getArg(v_decl_1675_, v___x_1829_);
lean_dec(v_decl_1675_);
if (v_reassignment_1674_ == 0)
{
lean_object* v___x_1831_; 
lean_dec(v_x_1821_);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1684_ = v___y_1826_;
v___y_1685_ = v___y_1825_;
v___y_1686_ = v_rhs_1830_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1827_;
v___y_1689_ = v___y_1828_;
v___y_1690_ = v___y_1823_;
v___y_1691_ = v___x_1831_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_mk_empty_array_with_capacity(v___x_1832_);
v___x_1834_ = lean_array_push(v___x_1833_, v_x_1821_);
v___y_1684_ = v___y_1826_;
v___y_1685_ = v___y_1825_;
v___y_1686_ = v_rhs_1830_;
v___y_1687_ = v___y_1824_;
v___y_1688_ = v___y_1827_;
v___y_1689_ = v___y_1828_;
v___y_1690_ = v___y_1823_;
v___y_1691_ = v___x_1834_;
goto v___jp_1683_;
}
}
}
v___jp_1683_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___y_1686_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1691_, v___x_1692_, v___x_1693_, v___x_1693_, v___y_1690_, v___y_1687_, v___y_1685_, v___y_1684_, v___y_1688_, v___y_1689_);
return v___x_1694_;
}
v___jp_1695_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___y_1697_);
if (lean_obj_tag(v___y_1698_) == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1699_, v___x_1706_, v___y_1696_, v___x_1707_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1708_;
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1710_; 
v_val_1709_ = lean_ctor_get(v___y_1698_, 0);
lean_inc(v_val_1709_);
lean_dec_ref(v___y_1698_);
v___x_1710_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1699_, v___x_1706_, v___y_1696_, v_val_1709_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_b_1987_);
return v___x_1996_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_array_uget_borrowed(v_as_1984_, v_i_1986_);
lean_inc(v_a_1997_);
v___x_1998_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1997_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1999_, v_b_1987_);
v___x_2001_ = ((size_t)1ULL);
v___x_2002_ = lean_usize_add(v_i_1986_, v___x_2001_);
v_i_1986_ = v___x_2002_;
v_b_1987_ = v___x_2000_;
goto _start;
}
else
{
lean_dec_ref(v_b_1987_);
return v___x_1998_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_a_2046_; uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_b_2037_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_a_2053_; uint8_t v___x_2054_; 
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2053_ = lean_array_uget_borrowed(v_as_2034_, v_i_2036_);
lean_inc(v_a_2053_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v_a_2053_, v___x_2052_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref(v___x_2055_);
v_a_2046_ = v_b_2037_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_b_2037_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2084_ = l_Lean_Syntax_getArg(v_a_2053_, v___x_2064_);
v___x_2085_ = l_Lean_Syntax_getArgs(v___x_2084_);
lean_dec(v___x_2084_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2088_ = lean_array_get_size(v___x_2085_);
v___x_2089_ = lean_nat_dec_lt(v___x_2086_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec_ref(v___x_2085_);
v___y_2067_ = v___x_2087_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_box(v___x_2054_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2087_);
v___x_2092_ = lean_nat_dec_le(v___x_2088_, v___x_2088_);
if (v___x_2092_ == 0)
{
if (v___x_2089_ == 0)
{
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2085_);
v___y_2067_ = v___x_2087_;
goto v___jp_2066_;
}
else
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v_snd_2096_; 
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = lean_usize_of_nat(v___x_2088_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2054_, v___x_2033_, v___x_2085_, v___x_2093_, v___x_2094_, v___x_2091_);
lean_dec_ref(v___x_2085_);
v_snd_2096_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_snd_2096_);
lean_dec_ref(v___x_2095_);
v___y_2067_ = v_snd_2096_;
goto v___jp_2066_;
}
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v_snd_2100_; 
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = lean_usize_of_nat(v___x_2088_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2054_, v___x_2033_, v___x_2085_, v___x_2097_, v___x_2098_, v___x_2091_);
lean_dec_ref(v___x_2085_);
v_snd_2100_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_snd_2100_);
lean_dec_ref(v___x_2099_);
v___y_2067_ = v_snd_2100_;
goto v___jp_2066_;
}
}
v___jp_2066_:
{
size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v_sz_2068_ = lean_array_size(v___y_2067_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2068_, v___x_2069_, v___y_2067_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref(v___x_2071_);
v_a_2046_ = v_b_2037_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_b_2037_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v___x_2070_);
v___x_2080_ = l_Lean_Syntax_getArg(v_a_2053_, v___x_2065_);
v___x_2081_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2080_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2037_, v_a_2082_);
v_a_2046_ = v___x_2083_;
goto v___jp_2045_;
}
else
{
lean_dec_ref(v_b_2037_);
return v___x_2081_;
}
}
}
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; 
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2036_, v___x_2047_);
v_i_2036_ = v___x_2048_;
v_b_2037_ = v_a_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2101_, size_t v_sz_2102_, size_t v_i_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_a_2113_; uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2103_, v_sz_2102_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_b_2104_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v_a_2120_ = lean_array_uget_borrowed(v_as_2101_, v_i_2103_);
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2120_);
v___x_2134_ = l_Lean_Syntax_isOfKind(v_a_2120_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2120_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v_a_2120_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2138_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2139_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2138_, v___x_2136_);
v___x_2140_ = l_Std_Format_defWidth;
v___x_2141_ = l_Std_Format_pretty(v___x_2139_, v___x_2140_, v___x_2119_, v___x_2119_);
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2137_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2143_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_dec_ref(v___x_2144_);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_b_2104_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2153_);
v___x_2155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2154_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v___x_2154_);
v___x_2157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2158_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2159_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2158_, v___x_2156_);
v___x_2160_ = l_Std_Format_defWidth;
v___x_2161_ = l_Std_Format_pretty(v___x_2159_, v___x_2160_, v___x_2119_, v___x_2119_);
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2163_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_dec_ref(v___x_2164_);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_b_2104_);
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
lean_object* v___x_2173_; lean_object* v___x_2174_; size_t v_sz_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2173_ = l_Lean_Syntax_getArg(v___x_2154_, v___x_2119_);
lean_dec(v___x_2154_);
v___x_2174_ = l_Lean_Syntax_getArgs(v___x_2173_);
lean_dec(v___x_2173_);
v_sz_2175_ = lean_array_size(v___x_2174_);
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2134_, v___x_2174_, v_sz_2175_, v___x_2176_, v_b_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___x_2174_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v_a_2113_ = v_a_2178_;
goto v___jp_2112_;
}
else
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(2u);
v___x_2180_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2179_);
v___x_2181_ = l_Lean_Syntax_isNone(v___x_2180_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = l_Lean_Syntax_matchesNull(v___x_2180_, v___x_2179_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2183_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2184_ = lean_box(0);
lean_inc(v_a_2120_);
v___x_2185_ = l_Lean_Syntax_formatStx(v_a_2120_, v___x_2184_, v___x_2182_);
v___x_2186_ = l_Std_Format_defWidth;
v___x_2187_ = l_Std_Format_pretty(v___x_2185_, v___x_2186_, v___x_2119_, v___x_2119_);
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2183_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2189_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref(v___x_2190_);
v_a_2113_ = v_b_2104_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_b_2104_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
v___y_2124_ = v___y_2107_;
v___y_2125_ = v___y_2108_;
v___y_2126_ = v___y_2109_;
v___y_2127_ = v___y_2110_;
goto v___jp_2121_;
}
}
else
{
lean_dec(v___x_2180_);
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
v___y_2124_ = v___y_2107_;
v___y_2125_ = v___y_2108_;
v___y_2126_ = v___y_2109_;
v___y_2127_ = v___y_2110_;
goto v___jp_2121_;
}
}
v___jp_2121_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(4u);
v___x_2129_ = l_Lean_Syntax_getArg(v_a_2120_, v___x_2128_);
v___x_2130_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2129_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2131_, v_b_2104_);
v_a_2113_ = v___x_2132_;
goto v___jp_2112_;
}
else
{
lean_dec_ref(v_b_2104_);
return v___x_2130_;
}
}
}
v___jp_2112_:
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2103_, v___x_2114_);
v_i_2103_ = v___x_2115_;
v_b_2104_ = v_a_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2199_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2210_; 
v_val_2209_ = lean_ctor_get(v_stx_x3f_2199_, 0);
lean_inc(v_val_2209_);
lean_dec_ref(v_stx_x3f_2199_);
v___x_2210_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2209_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2217_, lean_object* v_as_2218_, size_t v_sz_2219_, size_t v_i_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_a_2230_; uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_lt(v_i_2220_, v_sz_2219_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v_b_2221_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; lean_object* v_a_2237_; uint8_t v___x_2238_; 
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2237_ = lean_array_uget_borrowed(v_as_2218_, v_i_2220_);
lean_inc(v_a_2237_);
v___x_2238_ = l_Lean_Syntax_isOfKind(v_a_2237_, v___x_2236_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_dec_ref(v___x_2239_);
v_a_2230_ = v_b_2221_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec_ref(v_b_2221_);
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___y_2251_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_unsigned_to_nat(3u);
v___x_2268_ = l_Lean_Syntax_getArg(v_a_2237_, v___x_2248_);
v___x_2269_ = l_Lean_Syntax_getArgs(v___x_2268_);
lean_dec(v___x_2268_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2272_ = lean_array_get_size(v___x_2269_);
v___x_2273_ = lean_nat_dec_lt(v___x_2270_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v___x_2269_);
v___y_2251_ = v___x_2271_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = lean_box(v___x_2238_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2271_);
v___x_2276_ = lean_nat_dec_le(v___x_2272_, v___x_2272_);
if (v___x_2276_ == 0)
{
if (v___x_2273_ == 0)
{
lean_dec_ref(v___x_2275_);
lean_dec_ref(v___x_2269_);
v___y_2251_ = v___x_2271_;
goto v___jp_2250_;
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; lean_object* v_snd_2280_; 
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2272_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2238_, v___x_2217_, v___x_2269_, v___x_2277_, v___x_2278_, v___x_2275_);
lean_dec_ref(v___x_2269_);
v_snd_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2279_);
v___y_2251_ = v_snd_2280_;
goto v___jp_2250_;
}
}
else
{
size_t v___x_2281_; size_t v___x_2282_; lean_object* v___x_2283_; lean_object* v_snd_2284_; 
v___x_2281_ = ((size_t)0ULL);
v___x_2282_ = lean_usize_of_nat(v___x_2272_);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2238_, v___x_2217_, v___x_2269_, v___x_2281_, v___x_2282_, v___x_2275_);
lean_dec_ref(v___x_2269_);
v_snd_2284_ = lean_ctor_get(v___x_2283_, 1);
lean_inc(v_snd_2284_);
lean_dec_ref(v___x_2283_);
v___y_2251_ = v_snd_2284_;
goto v___jp_2250_;
}
}
v___jp_2250_:
{
size_t v_sz_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v_sz_2252_ = lean_array_size(v___y_2251_);
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_sz_2252_, v___x_2253_, v___y_2251_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref(v___x_2255_);
v_a_2230_ = v_b_2221_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_b_2221_);
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
lean_dec_ref(v___x_2254_);
v___x_2264_ = l_Lean_Syntax_getArg(v_a_2237_, v___x_2249_);
v___x_2265_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2264_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2221_, v_a_2266_);
v_a_2230_ = v___x_2267_;
goto v___jp_2229_;
}
else
{
lean_dec_ref(v_b_2221_);
return v___x_2265_;
}
}
}
}
}
v___jp_2229_:
{
size_t v___x_2231_; size_t v___x_2232_; 
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = lean_usize_add(v_i_2220_, v___x_2231_);
v_i_2220_ = v___x_2232_;
v_b_2221_ = v_a_2230_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2321_ = l_Lean_NameSet_empty;
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = 0;
v___x_2324_ = 1;
v___x_2325_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2325_, 0, v___x_2322_);
lean_ctor_set(v___x_2325_, 1, v___x_2321_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2, v___x_2324_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2 + 1, v___x_2323_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2 + 2, v___x_2323_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2 + 3, v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2348_; lean_object* v_bodyInfo_2349_; lean_object* v___y_2353_; lean_object* v_bodyInfo_2354_; lean_object* v___x_2357_; lean_object* v_env_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2357_ = lean_st_ref_get(v_a_2332_);
v_env_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_ref(v_env_2358_);
lean_dec(v___x_2357_);
lean_inc(v_stx_2326_);
v___x_2359_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2359_, 0, v_env_2358_);
lean_closure_set(v___x_2359_, 1, v_stx_2326_);
v___x_2360_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2359_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_4419_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_4419_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_4419_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
if (lean_obj_tag(v_a_2361_) == 1)
{
lean_object* v_val_2365_; lean_object* v_snd_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_del_object(v___x_2363_);
lean_dec(v_stx_2326_);
v_val_2365_ = lean_ctor_get(v_a_2361_, 0);
lean_inc(v_val_2365_);
lean_dec_ref(v_a_2361_);
v_snd_2366_ = lean_ctor_get(v_val_2365_, 1);
lean_inc(v_snd_2366_);
lean_dec(v_val_2365_);
v___x_2367_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2367_, 0, lean_box(0));
lean_closure_set(v___x_2367_, 1, v_snd_2366_);
v___x_2368_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2367_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
v_stx_2326_ = v_a_2369_;
goto _start;
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2368_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2368_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___x_2561_; uint8_t v___x_2562_; uint8_t v___x_2563_; 
lean_dec(v_a_2361_);
v___x_2561_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(v_stx_2326_);
v___x_2562_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2561_);
v___x_2563_ = 1;
if (v___x_2562_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(v_stx_2326_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(v_stx_2326_);
v___x_2567_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(v_stx_2326_);
v___x_2569_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(v_stx_2326_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2326_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; uint8_t v___x_2575_; 
lean_del_object(v___x_2363_);
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2326_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2326_);
v___x_2577_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; 
v___x_2578_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2326_);
v___x_2579_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2326_);
v___x_2641_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2326_);
v___x_2643_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2326_);
v___x_2645_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2326_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2326_);
v___x_2649_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2326_);
v___x_2651_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2326_);
v___x_2653_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2326_);
v___x_2655_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2326_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50));
lean_inc(v_stx_2326_);
v___x_2659_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2326_);
v___x_2661_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2326_);
v___x_2663_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2326_);
v___x_2665_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2326_);
v___x_2667_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2326_);
v___x_2669_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2326_);
v___x_2671_ = l_Lean_Syntax_isOfKind(v_stx_2326_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v_env_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2672_ = lean_st_ref_get(v_a_2332_);
v_env_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref(v_env_2673_);
lean_dec(v___x_2672_);
lean_inc_n(v_stx_2326_, 2);
v___x_2674_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2675_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2676_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2675_, v_env_2673_, v___x_2674_);
v___x_2677_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2678_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2676_, v___x_2677_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2709_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2709_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2709_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_fst_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2707_; 
v_fst_2683_ = lean_ctor_get(v_a_2679_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v_a_2679_, 1);
lean_dec(v_unused_2708_);
v___x_2685_ = v_a_2679_;
v_isShared_2686_ = v_isSharedCheck_2707_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_fst_2683_);
lean_dec(v_a_2679_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2707_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
if (lean_obj_tag(v_fst_2683_) == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_del_object(v___x_2681_);
v___x_2687_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2688_ = l_Lean_MessageData_ofName(v___x_2674_);
lean_inc_ref(v___x_2688_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 7);
lean_ctor_set(v___x_2685_, 1, v___x_2688_);
lean_ctor_set(v___x_2685_, 0, v___x_2687_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2694_ = l_Lean_indentD(v___x_2693_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2692_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___x_2688_);
v___x_2699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2700_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_2701_;
}
}
else
{
lean_object* v_val_2703_; lean_object* v___x_2705_; 
lean_del_object(v___x_2685_);
lean_dec(v___x_2674_);
lean_dec(v_stx_2326_);
v_val_2703_ = lean_ctor_get(v_fst_2683_, 0);
lean_inc(v_val_2703_);
lean_dec_ref(v_fst_2683_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_val_2703_);
v___x_2705_ = v___x_2681_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_val_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v___x_2674_);
lean_dec(v_stx_2326_);
v_a_2710_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2678_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2678_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___y_2722_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_unsigned_to_nat(5u);
v___x_2720_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2719_);
v___x_2731_ = lean_unsigned_to_nat(6u);
v___x_2732_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2731_);
lean_dec(v_stx_2326_);
v___x_2733_ = l_Lean_Syntax_getOptional_x3f(v___x_2732_);
lean_dec(v___x_2732_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_box(0);
v___y_2722_ = v___x_2734_;
goto v___jp_2721_;
}
else
{
lean_object* v_val_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_val_2735_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_val_2735_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_val_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
v___y_2722_ = v___x_2740_;
goto v___jp_2721_;
}
}
}
v___jp_2721_:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2720_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2723_) == 0)
{
if (lean_obj_tag(v___y_2722_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref(v___x_2723_);
v___x_2725_ = l_Lean_NameSet_empty;
v___x_2726_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2726_, 0, v___x_2718_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*2, v___x_2669_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*2 + 1, v___x_2669_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*2 + 2, v___x_2669_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*2 + 3, v___x_2669_);
v___y_2348_ = v_a_2724_;
v_bodyInfo_2349_ = v___x_2726_;
goto v___jp_2347_;
}
else
{
lean_object* v_a_2727_; lean_object* v_val_2728_; lean_object* v___x_2729_; 
v_a_2727_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2723_);
v_val_2728_ = lean_ctor_get(v___y_2722_, 0);
lean_inc(v_val_2728_);
lean_dec_ref(v___y_2722_);
v___x_2729_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2728_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v___y_2348_ = v_a_2727_;
v_bodyInfo_2349_ = v_a_2730_;
goto v___jp_2347_;
}
else
{
lean_dec(v_a_2727_);
return v___x_2729_;
}
}
}
else
{
lean_dec(v___y_2722_);
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___y_2747_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_unsigned_to_nat(5u);
v___x_2745_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2744_);
v___x_2756_ = lean_unsigned_to_nat(6u);
v___x_2757_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2756_);
lean_dec(v_stx_2326_);
v___x_2758_ = l_Lean_Syntax_getOptional_x3f(v___x_2757_);
lean_dec(v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_box(0);
v___y_2747_ = v___x_2759_;
goto v___jp_2746_;
}
else
{
lean_object* v_val_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_val_2760_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2758_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_val_2760_);
lean_dec(v___x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_val_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2747_ = v___x_2765_;
goto v___jp_2746_;
}
}
}
v___jp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2745_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2748_) == 0)
{
if (lean_obj_tag(v___y_2747_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = l_Lean_NameSet_empty;
v___x_2751_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2751_, 0, v___x_2743_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2, v___x_2667_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 1, v___x_2667_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 2, v___x_2667_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2 + 3, v___x_2667_);
v___y_2353_ = v_a_2749_;
v_bodyInfo_2354_ = v___x_2751_;
goto v___jp_2352_;
}
else
{
lean_object* v_a_2752_; lean_object* v_val_2753_; lean_object* v___x_2754_; 
v_a_2752_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2748_);
v_val_2753_ = lean_ctor_get(v___y_2747_, 0);
lean_inc(v_val_2753_);
lean_dec_ref(v___y_2747_);
v___x_2754_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2753_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v___y_2353_ = v_a_2752_;
v_bodyInfo_2354_ = v_a_2755_;
goto v___jp_2352_;
}
else
{
lean_dec(v_a_2752_);
return v___x_2754_;
}
}
}
else
{
lean_dec(v___y_2747_);
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2983_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2769_);
v___x_2984_ = l_Lean_Syntax_isNone(v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_unsigned_to_nat(5u);
v___x_2986_ = l_Lean_Syntax_matchesNull(v___x_2983_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v_env_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2987_ = lean_st_ref_get(v_a_2332_);
v_env_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_ref(v_env_2988_);
lean_dec(v___x_2987_);
lean_inc_n(v_stx_2326_, 2);
v___x_2989_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2990_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2991_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2990_, v_env_2988_, v___x_2989_);
v___x_2992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2993_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2991_, v___x_2992_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_2991_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3024_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3024_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3024_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v_fst_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3022_; 
v_fst_2998_ = lean_ctor_get(v_a_2994_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_a_2994_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v_a_2994_, 1);
lean_dec(v_unused_3023_);
v___x_3000_ = v_a_2994_;
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_fst_2998_);
lean_dec(v_a_2994_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
if (lean_obj_tag(v_fst_2998_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
lean_del_object(v___x_2996_);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3003_ = l_Lean_MessageData_ofName(v___x_2989_);
lean_inc_ref(v___x_3003_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set_tag(v___x_3000_, 7);
lean_ctor_set(v___x_3000_, 1, v___x_3003_);
lean_ctor_set(v___x_3000_, 0, v___x_3002_);
v___x_3005_ = v___x_3000_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3006_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3009_ = l_Lean_indentD(v___x_3008_);
v___x_3010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3007_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3003_);
v___x_3014_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3015_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3016_;
}
}
else
{
lean_object* v_val_3018_; lean_object* v___x_3020_; 
lean_del_object(v___x_3000_);
lean_dec(v___x_2989_);
lean_dec(v_stx_2326_);
v_val_3018_ = lean_ctor_get(v_fst_2998_, 0);
lean_inc(v_val_3018_);
lean_dec_ref(v_fst_2998_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v_val_3018_);
v___x_3020_ = v___x_2996_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_val_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v___x_2989_);
lean_dec(v_stx_2326_);
v_a_3025_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2993_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2993_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
v___y_2771_ = v_a_2327_;
v___y_2772_ = v_a_2328_;
v___y_2773_ = v_a_2329_;
v___y_2774_ = v_a_2330_;
v___y_2775_ = v_a_2331_;
v___y_2776_ = v_a_2332_;
goto v___jp_2770_;
}
}
else
{
lean_dec(v___x_2983_);
v___y_2771_ = v_a_2327_;
v___y_2772_ = v_a_2328_;
v___y_2773_ = v_a_2329_;
v___y_2774_ = v_a_2330_;
v___y_2775_ = v_a_2331_;
v___y_2776_ = v_a_2332_;
goto v___jp_2770_;
}
v___jp_2770_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2777_ = lean_unsigned_to_nat(4u);
v___x_2778_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2777_);
v___x_2779_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v___x_2778_);
v___x_2780_ = l_Lean_Syntax_isOfKind(v___x_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v_env_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v___x_2778_);
v___x_2781_ = lean_st_ref_get(v___y_2776_);
v_env_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref(v_env_2782_);
lean_dec(v___x_2781_);
lean_inc_n(v_stx_2326_, 2);
v___x_2783_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2784_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2785_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2784_, v_env_2782_, v___x_2783_);
v___x_2786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2787_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2785_, v___x_2786_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___x_2785_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2818_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2818_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2818_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_fst_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2816_; 
v_fst_2792_ = lean_ctor_get(v_a_2788_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_a_2788_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v_a_2788_, 1);
lean_dec(v_unused_2817_);
v___x_2794_ = v_a_2788_;
v_isShared_2795_ = v_isSharedCheck_2816_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_fst_2792_);
lean_dec(v_a_2788_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2816_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
if (lean_obj_tag(v_fst_2792_) == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_del_object(v___x_2790_);
v___x_2796_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2797_ = l_Lean_MessageData_ofName(v___x_2783_);
lean_inc_ref(v___x_2797_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 7);
lean_ctor_set(v___x_2794_, 1, v___x_2797_);
lean_ctor_set(v___x_2794_, 0, v___x_2796_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2800_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2803_ = l_Lean_indentD(v___x_2802_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2801_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2797_);
v___x_2808_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2809_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2810_;
}
}
else
{
lean_object* v_val_2812_; lean_object* v___x_2814_; 
lean_del_object(v___x_2794_);
lean_dec(v___x_2783_);
lean_dec(v_stx_2326_);
v_val_2812_ = lean_ctor_get(v_fst_2792_, 0);
lean_inc(v_val_2812_);
lean_dec_ref(v_fst_2792_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_val_2812_);
v___x_2814_ = v___x_2790_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_val_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___x_2783_);
lean_dec(v_stx_2326_);
v_a_2819_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2787_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2787_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; size_t v_sz_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2827_ = l_Lean_Syntax_getArg(v___x_2778_, v___x_2768_);
v___x_2828_ = l_Lean_Syntax_getArgs(v___x_2827_);
lean_dec(v___x_2827_);
v_sz_2829_ = lean_array_size(v___x_2828_);
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v_sz_2829_, v___x_2830_, v___x_2828_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2832_; lean_object* v_env_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec(v___x_2778_);
v___x_2832_ = lean_st_ref_get(v___y_2776_);
v_env_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc_ref(v_env_2833_);
lean_dec(v___x_2832_);
lean_inc_n(v_stx_2326_, 2);
v___x_2834_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2835_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2836_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2835_, v_env_2833_, v___x_2834_);
v___x_2837_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2838_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2836_, v___x_2837_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___x_2836_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2869_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2869_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2869_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_fst_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2867_; 
v_fst_2843_ = lean_ctor_get(v_a_2839_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v_a_2839_, 1);
lean_dec(v_unused_2868_);
v___x_2845_ = v_a_2839_;
v_isShared_2846_ = v_isSharedCheck_2867_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_fst_2843_);
lean_dec(v_a_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2867_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
if (lean_obj_tag(v_fst_2843_) == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_del_object(v___x_2841_);
v___x_2847_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2848_ = l_Lean_MessageData_ofName(v___x_2834_);
lean_inc_ref(v___x_2848_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 7);
lean_ctor_set(v___x_2845_, 1, v___x_2848_);
lean_ctor_set(v___x_2845_, 0, v___x_2847_);
v___x_2850_ = v___x_2845_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2851_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2854_ = l_Lean_indentD(v___x_2853_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2852_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2848_);
v___x_2859_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2860_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2861_;
}
}
else
{
lean_object* v_val_2863_; lean_object* v___x_2865_; 
lean_del_object(v___x_2845_);
lean_dec(v___x_2834_);
lean_dec(v_stx_2326_);
v_val_2863_ = lean_ctor_get(v_fst_2843_, 0);
lean_inc(v_val_2863_);
lean_dec_ref(v_fst_2843_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_val_2863_);
v___x_2865_ = v___x_2841_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_val_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v___x_2834_);
lean_dec(v_stx_2326_);
v_a_2870_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2838_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2838_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_val_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_val_2878_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_val_2878_);
lean_dec_ref(v___x_2831_);
v___x_2879_ = l_Lean_Syntax_getArg(v___x_2778_, v___x_2769_);
lean_dec(v___x_2778_);
v___x_2880_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v___x_2879_);
v___x_2881_ = l_Lean_Syntax_isOfKind(v___x_2879_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v_env_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v___x_2879_);
lean_dec(v_val_2878_);
v___x_2882_ = lean_st_ref_get(v___y_2776_);
v_env_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_ref(v_env_2883_);
lean_dec(v___x_2882_);
lean_inc_n(v_stx_2326_, 2);
v___x_2884_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2885_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2886_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2885_, v_env_2883_, v___x_2884_);
v___x_2887_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2888_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2886_, v___x_2887_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
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
v___x_2897_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2898_ = l_Lean_MessageData_ofName(v___x_2884_);
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
v___x_2901_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2904_ = l_Lean_indentD(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2902_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___x_2898_);
v___x_2909_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2910_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2911_;
}
}
else
{
lean_object* v_val_2913_; lean_object* v___x_2915_; 
lean_del_object(v___x_2895_);
lean_dec(v___x_2884_);
lean_dec(v_stx_2326_);
v_val_2913_ = lean_ctor_get(v_fst_2893_, 0);
lean_inc(v_val_2913_);
lean_dec_ref(v_fst_2893_);
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
lean_dec(v___x_2884_);
lean_dec(v_stx_2326_);
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
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = l_Lean_Syntax_getArg(v___x_2879_, v___x_2769_);
v___x_2929_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
v___x_2930_ = l_Lean_Syntax_isOfKind(v___x_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec(v___x_2879_);
lean_dec(v_val_2878_);
v___x_2931_ = lean_st_ref_get(v___y_2776_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2931_);
lean_inc_n(v_stx_2326_, 2);
v___x_2933_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2934_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2935_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2934_, v_env_2932_, v___x_2933_);
v___x_2936_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2937_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2935_, v___x_2936_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___x_2935_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2968_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2968_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2968_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_fst_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2966_; 
v_fst_2942_ = lean_ctor_get(v_a_2938_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; 
v_unused_2967_ = lean_ctor_get(v_a_2938_, 1);
lean_dec(v_unused_2967_);
v___x_2944_ = v_a_2938_;
v_isShared_2945_ = v_isSharedCheck_2966_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_fst_2942_);
lean_dec(v_a_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2966_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
if (lean_obj_tag(v_fst_2942_) == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_del_object(v___x_2940_);
v___x_2946_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2947_ = l_Lean_MessageData_ofName(v___x_2933_);
lean_inc_ref(v___x_2947_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 7);
lean_ctor_set(v___x_2944_, 1, v___x_2947_);
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2949_ = v___x_2944_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2953_ = l_Lean_indentD(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2951_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___x_2947_);
v___x_2958_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2959_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2960_;
}
}
else
{
lean_object* v_val_2962_; lean_object* v___x_2964_; 
lean_del_object(v___x_2944_);
lean_dec(v___x_2933_);
lean_dec(v_stx_2326_);
v_val_2962_ = lean_ctor_get(v_fst_2942_, 0);
lean_inc(v_val_2962_);
lean_dec_ref(v_fst_2942_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v_val_2962_);
v___x_2964_ = v___x_2940_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_val_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v___x_2933_);
lean_dec(v_stx_2326_);
v_a_2969_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2937_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2937_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v_stx_2326_);
v___x_2977_ = lean_unsigned_to_nat(3u);
v___x_2978_ = l_Lean_Syntax_getArg(v___x_2879_, v___x_2977_);
lean_dec(v___x_2879_);
v___x_2979_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2978_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; size_t v_sz_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v_sz_2981_ = lean_array_size(v_val_2878_);
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2878_, v_sz_2981_, v___x_2830_, v_a_2980_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v_val_2878_);
return v___x_2982_;
}
else
{
lean_dec(v_val_2878_);
return v___x_2979_;
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
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec(v_stx_2326_);
v___x_3033_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
else
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec(v_stx_2326_);
v___x_3035_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v_stx_2326_);
v___x_3037_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec(v_stx_2326_);
v___x_3039_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; size_t v_sz_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3041_ = lean_unsigned_to_nat(2u);
v___x_3042_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_getArgs(v___x_3042_);
lean_dec(v___x_3042_);
v_sz_3044_ = lean_array_size(v___x_3043_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3044_, v___x_3045_, v___x_3043_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; lean_object* v_env_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3047_ = lean_st_ref_get(v_a_2332_);
v_env_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc_ref(v_env_3048_);
lean_dec(v___x_3047_);
lean_inc_n(v_stx_2326_, 2);
v___x_3049_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3050_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3051_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3050_, v_env_3048_, v___x_3049_);
v___x_3052_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3053_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3051_, v___x_3052_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3051_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3084_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3084_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3084_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v_fst_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3082_; 
v_fst_3058_ = lean_ctor_get(v_a_3054_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3054_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_a_3054_, 1);
lean_dec(v_unused_3083_);
v___x_3060_ = v_a_3054_;
v_isShared_3061_ = v_isSharedCheck_3082_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_fst_3058_);
lean_dec(v_a_3054_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3082_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_fst_3058_) == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
lean_del_object(v___x_3056_);
v___x_3062_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3063_ = l_Lean_MessageData_ofName(v___x_3049_);
lean_inc_ref(v___x_3063_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 7);
lean_ctor_set(v___x_3060_, 1, v___x_3063_);
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3069_ = l_Lean_indentD(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3067_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3063_);
v___x_3074_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3075_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3076_;
}
}
else
{
lean_object* v_val_3078_; lean_object* v___x_3080_; 
lean_del_object(v___x_3060_);
lean_dec(v___x_3049_);
lean_dec(v_stx_2326_);
v_val_3078_ = lean_ctor_get(v_fst_3058_, 0);
lean_inc(v_val_3078_);
lean_dec_ref(v_fst_3058_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v_val_3078_);
v___x_3080_ = v___x_3056_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_val_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v___x_3049_);
lean_dec(v_stx_2326_);
v_a_3085_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3053_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3053_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3227_; 
v_val_3093_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3095_ = v___x_3046_;
v_isShared_3096_ = v_isSharedCheck_3227_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___x_3046_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3227_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v_finSeq_x3f_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3097_ = lean_unsigned_to_nat(1u);
v___x_3098_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3097_);
v___x_3122_ = lean_unsigned_to_nat(3u);
v___x_3123_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_isNone(v___x_3123_);
if (v___x_3124_ == 0)
{
uint8_t v___x_3125_; 
lean_inc(v___x_3123_);
v___x_3125_ = l_Lean_Syntax_matchesNull(v___x_3123_, v___x_3097_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v_env_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v___x_3123_);
lean_dec(v___x_3098_);
lean_del_object(v___x_3095_);
lean_dec(v_val_3093_);
v___x_3126_ = lean_st_ref_get(v_a_2332_);
v_env_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_env_3127_);
lean_dec(v___x_3126_);
lean_inc_n(v_stx_2326_, 2);
v___x_3128_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3129_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3130_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3129_, v_env_3127_, v___x_3128_);
v___x_3131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3132_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3130_, v___x_3131_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3130_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3163_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3163_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3163_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v_fst_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3161_; 
v_fst_3137_ = lean_ctor_get(v_a_3133_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3133_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v_a_3133_, 1);
lean_dec(v_unused_3162_);
v___x_3139_ = v_a_3133_;
v_isShared_3140_ = v_isSharedCheck_3161_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_fst_3137_);
lean_dec(v_a_3133_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3161_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
if (lean_obj_tag(v_fst_3137_) == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_del_object(v___x_3135_);
v___x_3141_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3142_ = l_Lean_MessageData_ofName(v___x_3128_);
lean_inc_ref(v___x_3142_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 7);
lean_ctor_set(v___x_3139_, 1, v___x_3142_);
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3144_ = v___x_3139_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3145_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3148_ = l_Lean_indentD(v___x_3147_);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3149_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v___x_3142_);
v___x_3153_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3154_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3155_;
}
}
else
{
lean_object* v_val_3157_; lean_object* v___x_3159_; 
lean_del_object(v___x_3139_);
lean_dec(v___x_3128_);
lean_dec(v_stx_2326_);
v_val_3157_ = lean_ctor_get(v_fst_3137_, 0);
lean_inc(v_val_3157_);
lean_dec_ref(v_fst_3137_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_val_3157_);
v___x_3159_ = v___x_3135_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_val_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v___x_3128_);
lean_dec(v_stx_2326_);
v_a_3164_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3132_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3132_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l_Lean_Syntax_getArg(v___x_3123_, v___x_3172_);
lean_dec(v___x_3123_);
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_3173_);
v___x_3175_ = l_Lean_Syntax_isOfKind(v___x_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v_env_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v___x_3173_);
lean_dec(v___x_3098_);
lean_del_object(v___x_3095_);
lean_dec(v_val_3093_);
v___x_3176_ = lean_st_ref_get(v_a_2332_);
v_env_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3176_);
lean_inc_n(v_stx_2326_, 2);
v___x_3178_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3179_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3180_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3179_, v_env_3177_, v___x_3178_);
v___x_3181_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3182_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3180_, v___x_3181_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3180_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3213_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3213_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3213_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_fst_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3211_; 
v_fst_3187_ = lean_ctor_get(v_a_3183_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_a_3183_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v_a_3183_, 1);
lean_dec(v_unused_3212_);
v___x_3189_ = v_a_3183_;
v_isShared_3190_ = v_isSharedCheck_3211_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_fst_3187_);
lean_dec(v_a_3183_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3211_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
if (lean_obj_tag(v_fst_3187_) == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_del_object(v___x_3185_);
v___x_3191_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3192_ = l_Lean_MessageData_ofName(v___x_3178_);
lean_inc_ref(v___x_3192_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 7);
lean_ctor_set(v___x_3189_, 1, v___x_3192_);
lean_ctor_set(v___x_3189_, 0, v___x_3191_);
v___x_3194_ = v___x_3189_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3195_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3198_ = l_Lean_indentD(v___x_3197_);
v___x_3199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3196_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3199_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3192_);
v___x_3203_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3204_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3205_;
}
}
else
{
lean_object* v_val_3207_; lean_object* v___x_3209_; 
lean_del_object(v___x_3189_);
lean_dec(v___x_3178_);
lean_dec(v_stx_2326_);
v_val_3207_ = lean_ctor_get(v_fst_3187_, 0);
lean_inc(v_val_3207_);
lean_dec_ref(v_fst_3187_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_val_3207_);
v___x_3209_ = v___x_3185_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_val_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v___x_3178_);
lean_dec(v_stx_2326_);
v_a_3214_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3182_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3182_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_dec(v_stx_2326_);
v___x_3222_ = l_Lean_Syntax_getArg(v___x_3173_, v___x_3097_);
lean_dec(v___x_3173_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3222_);
v___x_3224_ = v___x_3095_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
v_finSeq_x3f_3100_ = v___x_3224_;
v___y_3101_ = v_a_2327_;
v___y_3102_ = v_a_2328_;
v___y_3103_ = v_a_2329_;
v___y_3104_ = v_a_2330_;
v___y_3105_ = v_a_2331_;
v___y_3106_ = v_a_2332_;
goto v___jp_3099_;
}
}
}
}
else
{
lean_object* v___x_3226_; 
lean_dec(v___x_3123_);
lean_del_object(v___x_3095_);
lean_dec(v_stx_2326_);
v___x_3226_ = lean_box(0);
v_finSeq_x3f_3100_ = v___x_3226_;
v___y_3101_ = v_a_2327_;
v___y_3102_ = v_a_2328_;
v___y_3103_ = v_a_2329_;
v___y_3104_ = v_a_2330_;
v___y_3105_ = v_a_2331_;
v___y_3106_ = v_a_2332_;
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3098_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; size_t v_sz_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v___x_3107_);
v_sz_3109_ = lean_array_size(v_val_3093_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3093_, v_sz_3109_, v___x_3045_, v_a_3108_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v_val_3093_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
v___x_3112_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3121_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3111_, v_a_3113_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3117_);
v___x_3119_ = v___x_3115_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
else
{
lean_dec(v_a_3111_);
return v___x_3112_;
}
}
else
{
lean_dec(v_finSeq_x3f_3100_);
return v___x_3110_;
}
}
else
{
lean_dec(v_finSeq_x3f_3100_);
lean_dec(v_val_3093_);
return v___x_3107_;
}
}
}
}
}
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3228_);
lean_dec(v_stx_2326_);
v___x_3230_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3229_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3255_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3255_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3255_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
uint8_t v_breaks_3235_; uint8_t v_returnsEarly_3236_; lean_object* v_reassigns_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3253_; 
v_breaks_3235_ = lean_ctor_get_uint8(v_a_3231_, sizeof(void*)*2);
v_returnsEarly_3236_ = lean_ctor_get_uint8(v_a_3231_, sizeof(void*)*2 + 2);
v_reassigns_3237_ = lean_ctor_get(v_a_3231_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_a_3231_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_a_3231_, 0);
lean_dec(v_unused_3254_);
v___x_3239_ = v_a_3231_;
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_reassigns_3237_);
lean_dec(v_a_3231_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3251_; 
if (v_breaks_3235_ == 0)
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v___y_3251_ = v___x_3252_;
goto v___jp_3250_;
}
else
{
v___y_3251_ = v___x_3228_;
goto v___jp_3250_;
}
v___jp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___y_3242_);
v___x_3245_ = v___x_3239_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___y_3242_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_reassigns_3237_);
lean_ctor_set_uint8(v_reuseFailAlloc_3249_, sizeof(void*)*2 + 2, v_returnsEarly_3236_);
v___x_3245_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*2, v___x_2653_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*2 + 1, v___x_2653_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*2 + 3, v___y_3243_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3245_);
v___x_3247_ = v___x_3233_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3250_:
{
if (v_breaks_3235_ == 0)
{
v___y_3242_ = v___y_3251_;
v___y_3243_ = v___x_2655_;
goto v___jp_3241_;
}
else
{
v___y_3242_ = v___y_3251_;
v___y_3243_ = v___x_2653_;
goto v___jp_3241_;
}
}
}
}
}
else
{
return v___x_3230_;
}
}
}
else
{
lean_object* v___x_3256_; lean_object* v___y_3258_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3256_ = lean_unsigned_to_nat(1u);
v___x_3329_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3256_);
v___x_3330_ = l_Lean_Syntax_getArgs(v___x_3329_);
lean_dec(v___x_3329_);
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3333_ = lean_array_get_size(v___x_3330_);
v___x_3334_ = lean_nat_dec_lt(v___x_3331_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_dec_ref(v___x_3330_);
v___y_3258_ = v___x_3332_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = lean_box(v___x_2653_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3332_);
v___x_3337_ = lean_nat_dec_le(v___x_3333_, v___x_3333_);
if (v___x_3337_ == 0)
{
if (v___x_3334_ == 0)
{
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___x_3330_);
v___y_3258_ = v___x_3332_;
goto v___jp_3257_;
}
else
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; lean_object* v_snd_3341_; 
v___x_3338_ = ((size_t)0ULL);
v___x_3339_ = lean_usize_of_nat(v___x_3333_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2653_, v___x_2651_, v___x_3330_, v___x_3338_, v___x_3339_, v___x_3336_);
lean_dec_ref(v___x_3330_);
v_snd_3341_ = lean_ctor_get(v___x_3340_, 1);
lean_inc(v_snd_3341_);
lean_dec_ref(v___x_3340_);
v___y_3258_ = v_snd_3341_;
goto v___jp_3257_;
}
}
else
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; lean_object* v_snd_3345_; 
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = lean_usize_of_nat(v___x_3333_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2653_, v___x_2651_, v___x_3330_, v___x_3342_, v___x_3343_, v___x_3336_);
lean_dec_ref(v___x_3330_);
v_snd_3345_ = lean_ctor_get(v___x_3344_, 1);
lean_inc(v_snd_3345_);
lean_dec_ref(v___x_3344_);
v___y_3258_ = v_snd_3345_;
goto v___jp_3257_;
}
}
v___jp_3257_:
{
size_t v_sz_3259_; size_t v___x_3260_; lean_object* v___x_3261_; 
v_sz_3259_ = lean_array_size(v___y_3258_);
v___x_3260_ = ((size_t)0ULL);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3259_, v___x_3260_, v___y_3258_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3262_; lean_object* v_env_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3262_ = lean_st_ref_get(v_a_2332_);
v_env_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc_ref(v_env_3263_);
lean_dec(v___x_3262_);
lean_inc_n(v_stx_2326_, 2);
v___x_3264_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3265_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3266_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3265_, v_env_3263_, v___x_3264_);
v___x_3267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3268_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3266_, v___x_3267_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3266_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3299_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3299_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3299_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_fst_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3297_; 
v_fst_3273_ = lean_ctor_get(v_a_3269_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_a_3269_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v_a_3269_, 1);
lean_dec(v_unused_3298_);
v___x_3275_ = v_a_3269_;
v_isShared_3276_ = v_isSharedCheck_3297_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_fst_3273_);
lean_dec(v_a_3269_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3297_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
if (lean_obj_tag(v_fst_3273_) == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
lean_del_object(v___x_3271_);
v___x_3277_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3278_ = l_Lean_MessageData_ofName(v___x_3264_);
lean_inc_ref(v___x_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 7);
lean_ctor_set(v___x_3275_, 1, v___x_3278_);
lean_ctor_set(v___x_3275_, 0, v___x_3277_);
v___x_3280_ = v___x_3275_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3281_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3284_ = l_Lean_indentD(v___x_3283_);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3282_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v___x_3278_);
v___x_3289_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3290_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3291_;
}
}
else
{
lean_object* v_val_3293_; lean_object* v___x_3295_; 
lean_del_object(v___x_3275_);
lean_dec(v___x_3264_);
lean_dec(v_stx_2326_);
v_val_3293_ = lean_ctor_get(v_fst_3273_, 0);
lean_inc(v_val_3293_);
lean_dec_ref(v_fst_3273_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_val_3293_);
v___x_3295_ = v___x_3271_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_val_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v___x_3264_);
lean_dec(v_stx_2326_);
v_a_3300_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3268_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3268_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec_ref(v___x_3261_);
v___x_3308_ = lean_unsigned_to_nat(3u);
v___x_3309_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3308_);
lean_dec(v_stx_2326_);
v___x_3310_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3309_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3328_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3328_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3328_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
uint8_t v_returnsEarly_3315_; lean_object* v_reassigns_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3326_; 
v_returnsEarly_3315_ = lean_ctor_get_uint8(v_a_3311_, sizeof(void*)*2 + 2);
v_reassigns_3316_ = lean_ctor_get(v_a_3311_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_a_3311_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v_a_3311_, 0);
lean_dec(v_unused_3327_);
v___x_3318_ = v_a_3311_;
v_isShared_3319_ = v_isSharedCheck_3326_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_reassigns_3316_);
lean_dec(v_a_3311_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3326_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3256_);
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_reassigns_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3325_, sizeof(void*)*2 + 2, v_returnsEarly_3315_);
v___x_3321_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3323_; 
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*2, v___x_2651_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*2 + 1, v___x_2651_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*2 + 3, v___x_2651_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3321_);
v___x_3323_ = v___x_3313_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
else
{
return v___x_3310_;
}
}
}
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3346_ = lean_unsigned_to_nat(1u);
v___x_3347_ = lean_unsigned_to_nat(3u);
v___x_3348_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3347_);
lean_dec(v_stx_2326_);
v___x_3349_ = l_Lean_NameSet_empty;
v___x_3350_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3350_, 0, v___x_3346_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*2, v___x_2649_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*2 + 1, v___x_2649_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*2 + 2, v___x_2649_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*2 + 3, v___x_2649_);
v___x_3351_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3348_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3360_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3350_, v_a_3352_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3356_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_dec_ref(v___x_3350_);
return v___x_3351_;
}
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; size_t v_sz_3364_; size_t v___x_3365_; lean_object* v___x_3366_; 
v___x_3361_ = lean_unsigned_to_nat(4u);
v___x_3362_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3361_);
v___x_3363_ = l_Lean_Syntax_getArgs(v___x_3362_);
lean_dec(v___x_3362_);
v_sz_3364_ = lean_array_size(v___x_3363_);
v___x_3365_ = ((size_t)0ULL);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3364_, v___x_3365_, v___x_3363_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; lean_object* v_env_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3367_ = lean_st_ref_get(v_a_2332_);
v_env_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref(v_env_3368_);
lean_dec(v___x_3367_);
lean_inc_n(v_stx_2326_, 2);
v___x_3369_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3370_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3371_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3370_, v_env_3368_, v___x_3369_);
v___x_3372_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3373_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3371_, v___x_3372_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3371_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3404_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3404_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3404_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fst_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3402_; 
v_fst_3378_ = lean_ctor_get(v_a_3374_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_a_3374_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_a_3374_, 1);
lean_dec(v_unused_3403_);
v___x_3380_ = v_a_3374_;
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_fst_3378_);
lean_dec(v_a_3374_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
if (lean_obj_tag(v_fst_3378_) == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_del_object(v___x_3376_);
v___x_3382_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3383_ = l_Lean_MessageData_ofName(v___x_3369_);
lean_inc_ref(v___x_3383_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 7);
lean_ctor_set(v___x_3380_, 1, v___x_3383_);
lean_ctor_set(v___x_3380_, 0, v___x_3382_);
v___x_3385_ = v___x_3380_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3389_ = l_Lean_indentD(v___x_3388_);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3387_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3383_);
v___x_3394_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3395_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3396_;
}
}
else
{
lean_object* v_val_3398_; lean_object* v___x_3400_; 
lean_del_object(v___x_3380_);
lean_dec(v___x_3369_);
lean_dec(v_stx_2326_);
v_val_3398_ = lean_ctor_get(v_fst_3378_, 0);
lean_inc(v_val_3398_);
lean_dec_ref(v_fst_3378_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v_val_3398_);
v___x_3400_ = v___x_3376_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_val_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v___x_3369_);
lean_dec(v_stx_2326_);
v_a_3405_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3373_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3373_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3500_; 
v_val_3413_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3415_ = v___x_3366_;
v_isShared_3416_ = v_isSharedCheck_3500_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v___x_3366_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3500_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v_elseSeq_x3f_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3417_ = lean_unsigned_to_nat(3u);
v___x_3418_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3417_);
v___x_3443_ = lean_unsigned_to_nat(5u);
v___x_3444_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3443_);
v___x_3445_ = l_Lean_Syntax_isNone(v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3444_);
v___x_3447_ = l_Lean_Syntax_matchesNull(v___x_3444_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v_env_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v___x_3444_);
lean_dec(v___x_3418_);
lean_del_object(v___x_3415_);
lean_dec(v_val_3413_);
v___x_3448_ = lean_st_ref_get(v_a_2332_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
lean_inc_n(v_stx_2326_, 2);
v___x_3450_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3451_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3452_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3451_, v_env_3449_, v___x_3450_);
v___x_3453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3454_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3452_, v___x_3453_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3452_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3485_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3485_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3485_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_fst_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3483_; 
v_fst_3459_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_a_3455_, 1);
lean_dec(v_unused_3484_);
v___x_3461_ = v_a_3455_;
v_isShared_3462_ = v_isSharedCheck_3483_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_fst_3459_);
lean_dec(v_a_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3483_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
if (lean_obj_tag(v_fst_3459_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_del_object(v___x_3457_);
v___x_3463_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3464_ = l_Lean_MessageData_ofName(v___x_3450_);
lean_inc_ref(v___x_3464_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 7);
lean_ctor_set(v___x_3461_, 1, v___x_3464_);
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3467_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3470_ = l_Lean_indentD(v___x_3469_);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3468_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3464_);
v___x_3475_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3476_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3477_;
}
}
else
{
lean_object* v_val_3479_; lean_object* v___x_3481_; 
lean_del_object(v___x_3461_);
lean_dec(v___x_3450_);
lean_dec(v_stx_2326_);
v_val_3479_ = lean_ctor_get(v_fst_3459_, 0);
lean_inc(v_val_3479_);
lean_dec_ref(v_fst_3459_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_val_3479_);
v___x_3481_ = v___x_3457_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_val_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v___x_3450_);
lean_dec(v_stx_2326_);
v_a_3486_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3454_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3454_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
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
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_dec(v_stx_2326_);
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = l_Lean_Syntax_getArg(v___x_3444_, v___x_3494_);
lean_dec(v___x_3444_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3495_);
v___x_3497_ = v___x_3415_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
v_elseSeq_x3f_3420_ = v___x_3497_;
v___y_3421_ = v_a_2327_;
v___y_3422_ = v_a_2328_;
v___y_3423_ = v_a_2329_;
v___y_3424_ = v_a_2330_;
v___y_3425_ = v_a_2331_;
v___y_3426_ = v_a_2332_;
goto v___jp_3419_;
}
}
}
else
{
lean_object* v___x_3499_; 
lean_dec(v___x_3444_);
lean_del_object(v___x_3415_);
lean_dec(v_stx_2326_);
v___x_3499_ = lean_box(0);
v_elseSeq_x3f_3420_ = v___x_3499_;
v___y_3421_ = v_a_2327_;
v___y_3422_ = v_a_2328_;
v___y_3423_ = v_a_2329_;
v___y_3424_ = v_a_2330_;
v___y_3425_ = v_a_2331_;
v___y_3426_ = v_a_2332_;
goto v___jp_3419_;
}
v___jp_3419_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; size_t v_sz_3430_; lean_object* v___x_3431_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = l_Array_reverse___redArg(v_val_3413_);
v_sz_3430_ = lean_array_size(v___x_3429_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3429_, v_sz_3430_, v___x_3365_, v_a_3428_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___x_3429_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3418_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3442_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3434_, v_a_3432_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_dec(v_a_3432_);
return v___x_3433_;
}
}
else
{
lean_dec(v___x_3418_);
return v___x_3431_;
}
}
else
{
lean_dec(v___x_3418_);
lean_dec(v_val_3413_);
return v___x_3427_;
}
}
}
}
}
}
else
{
lean_object* v___x_3501_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___x_3565_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3565_ = lean_unsigned_to_nat(1u);
v___x_3672_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3565_);
v___x_3673_ = l_Lean_Syntax_isNone(v___x_3672_);
if (v___x_3673_ == 0)
{
uint8_t v___x_3674_; 
lean_inc(v___x_3672_);
v___x_3674_ = l_Lean_Syntax_matchesNull(v___x_3672_, v___x_3565_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v_env_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec(v___x_3672_);
v___x_3675_ = lean_st_ref_get(v_a_2332_);
v_env_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc_ref(v_env_3676_);
lean_dec(v___x_3675_);
lean_inc_n(v_stx_2326_, 2);
v___x_3677_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3678_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3679_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3678_, v_env_3676_, v___x_3677_);
v___x_3680_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3681_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3679_, v___x_3680_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3679_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3712_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3712_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3712_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v_fst_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3710_; 
v_fst_3686_ = lean_ctor_get(v_a_3682_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_a_3682_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v_a_3682_, 1);
lean_dec(v_unused_3711_);
v___x_3688_ = v_a_3682_;
v_isShared_3689_ = v_isSharedCheck_3710_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_fst_3686_);
lean_dec(v_a_3682_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3710_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
if (lean_obj_tag(v_fst_3686_) == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_del_object(v___x_3684_);
v___x_3690_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3691_ = l_Lean_MessageData_ofName(v___x_3677_);
lean_inc_ref(v___x_3691_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 7);
lean_ctor_set(v___x_3688_, 1, v___x_3691_);
lean_ctor_set(v___x_3688_, 0, v___x_3690_);
v___x_3693_ = v___x_3688_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3694_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3697_ = l_Lean_indentD(v___x_3696_);
v___x_3698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3695_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
lean_ctor_set(v___x_3701_, 1, v___x_3691_);
v___x_3702_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3703_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3704_;
}
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3708_; 
lean_del_object(v___x_3688_);
lean_dec(v___x_3677_);
lean_dec(v_stx_2326_);
v_val_3706_ = lean_ctor_get(v_fst_3686_, 0);
lean_inc(v_val_3706_);
lean_dec_ref(v_fst_3686_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v_val_3706_);
v___x_3708_ = v___x_3684_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_val_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v___x_3677_);
lean_dec(v_stx_2326_);
v_a_3713_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3681_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3681_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3721_ = l_Lean_Syntax_getArg(v___x_3672_, v___x_3501_);
lean_dec(v___x_3672_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3723_ = l_Lean_Syntax_isOfKind(v___x_3721_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; lean_object* v_env_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3724_ = lean_st_ref_get(v_a_2332_);
v_env_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc_ref(v_env_3725_);
lean_dec(v___x_3724_);
lean_inc_n(v_stx_2326_, 2);
v___x_3726_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3727_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3728_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3727_, v_env_3725_, v___x_3726_);
v___x_3729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3730_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3728_, v___x_3729_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3728_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3761_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3761_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3761_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_fst_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3759_; 
v_fst_3735_ = lean_ctor_get(v_a_3731_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3731_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v_a_3731_, 1);
lean_dec(v_unused_3760_);
v___x_3737_ = v_a_3731_;
v_isShared_3738_ = v_isSharedCheck_3759_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_fst_3735_);
lean_dec(v_a_3731_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3759_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
if (lean_obj_tag(v_fst_3735_) == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_del_object(v___x_3733_);
v___x_3739_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3740_ = l_Lean_MessageData_ofName(v___x_3726_);
lean_inc_ref(v___x_3740_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set_tag(v___x_3737_, 7);
lean_ctor_set(v___x_3737_, 1, v___x_3740_);
lean_ctor_set(v___x_3737_, 0, v___x_3739_);
v___x_3742_ = v___x_3737_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3743_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3746_ = l_Lean_indentD(v___x_3745_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3744_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set(v___x_3750_, 1, v___x_3740_);
v___x_3751_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3752_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3753_;
}
}
else
{
lean_object* v_val_3755_; lean_object* v___x_3757_; 
lean_del_object(v___x_3737_);
lean_dec(v___x_3726_);
lean_dec(v_stx_2326_);
v_val_3755_ = lean_ctor_get(v_fst_3735_, 0);
lean_inc(v_val_3755_);
lean_dec_ref(v_fst_3735_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v_val_3755_);
v___x_3757_ = v___x_3733_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_val_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v___x_3726_);
lean_dec(v_stx_2326_);
v_a_3762_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3730_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3730_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
v___y_3567_ = v_a_2327_;
v___y_3568_ = v_a_2328_;
v___y_3569_ = v_a_2329_;
v___y_3570_ = v_a_2330_;
v___y_3571_ = v_a_2331_;
v___y_3572_ = v_a_2332_;
goto v___jp_3566_;
}
}
}
else
{
lean_dec(v___x_3672_);
v___y_3567_ = v_a_2327_;
v___y_3568_ = v_a_2328_;
v___y_3569_ = v_a_2329_;
v___y_3570_ = v_a_2330_;
v___y_3571_ = v_a_2331_;
v___y_3572_ = v_a_2332_;
goto v___jp_3566_;
}
v___jp_3502_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3509_ = lean_unsigned_to_nat(6u);
v___x_3510_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3509_);
v___x_3511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_3510_);
v___x_3512_ = l_Lean_Syntax_isOfKind(v___x_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v_env_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec(v___x_3510_);
v___x_3513_ = lean_st_ref_get(v___y_3508_);
v_env_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc_ref(v_env_3514_);
lean_dec(v___x_3513_);
lean_inc_n(v_stx_2326_, 2);
v___x_3515_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3516_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3517_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3516_, v_env_3514_, v___x_3515_);
v___x_3518_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3519_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3517_, v___x_3518_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___x_3517_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3550_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3550_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3550_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v_fst_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3548_; 
v_fst_3524_ = lean_ctor_get(v_a_3520_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; 
v_unused_3549_ = lean_ctor_get(v_a_3520_, 1);
lean_dec(v_unused_3549_);
v___x_3526_ = v_a_3520_;
v_isShared_3527_ = v_isSharedCheck_3548_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_fst_3524_);
lean_dec(v_a_3520_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3548_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
if (lean_obj_tag(v_fst_3524_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_del_object(v___x_3522_);
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3529_ = l_Lean_MessageData_ofName(v___x_3515_);
lean_inc_ref(v___x_3529_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 7);
lean_ctor_set(v___x_3526_, 1, v___x_3529_);
lean_ctor_set(v___x_3526_, 0, v___x_3528_);
v___x_3531_ = v___x_3526_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3532_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3535_ = l_Lean_indentD(v___x_3534_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3533_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
lean_ctor_set(v___x_3539_, 1, v___x_3529_);
v___x_3540_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3541_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
return v___x_3542_;
}
}
else
{
lean_object* v_val_3544_; lean_object* v___x_3546_; 
lean_del_object(v___x_3526_);
lean_dec(v___x_3515_);
lean_dec(v_stx_2326_);
v_val_3544_ = lean_ctor_get(v_fst_3524_, 0);
lean_inc(v_val_3544_);
lean_dec_ref(v_fst_3524_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v_val_3544_);
v___x_3546_ = v___x_3522_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_val_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v___x_3515_);
lean_dec(v_stx_2326_);
v_a_3551_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3519_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3519_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; size_t v_sz_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
lean_dec(v_stx_2326_);
v___x_3559_ = l_Lean_Syntax_getArg(v___x_3510_, v___x_3501_);
lean_dec(v___x_3510_);
v___x_3560_ = l_Lean_Syntax_getArgs(v___x_3559_);
lean_dec(v___x_3559_);
v___x_3561_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_3562_ = lean_array_size(v___x_3560_);
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2645_, v___x_3560_, v_sz_3562_, v___x_3563_, v___x_3561_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec_ref(v___x_3560_);
return v___x_3564_;
}
}
v___jp_3566_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(2u);
v___x_3574_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3573_);
v___x_3575_ = l_Lean_Syntax_isNone(v___x_3574_);
if (v___x_3575_ == 0)
{
uint8_t v___x_3576_; 
lean_inc(v___x_3574_);
v___x_3576_ = l_Lean_Syntax_matchesNull(v___x_3574_, v___x_3565_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v_env_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v___x_3574_);
v___x_3577_ = lean_st_ref_get(v___y_3572_);
v_env_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc_ref(v_env_3578_);
lean_dec(v___x_3577_);
lean_inc_n(v_stx_2326_, 2);
v___x_3579_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3580_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3581_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3580_, v_env_3578_, v___x_3579_);
v___x_3582_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3583_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3581_, v___x_3582_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___x_3581_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3614_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3614_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3614_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_fst_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3612_; 
v_fst_3588_ = lean_ctor_get(v_a_3584_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v_a_3584_, 1);
lean_dec(v_unused_3613_);
v___x_3590_ = v_a_3584_;
v_isShared_3591_ = v_isSharedCheck_3612_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_fst_3588_);
lean_dec(v_a_3584_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3612_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
if (lean_obj_tag(v_fst_3588_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
lean_del_object(v___x_3586_);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3593_ = l_Lean_MessageData_ofName(v___x_3579_);
lean_inc_ref(v___x_3593_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 7);
lean_ctor_set(v___x_3590_, 1, v___x_3593_);
lean_ctor_set(v___x_3590_, 0, v___x_3592_);
v___x_3595_ = v___x_3590_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3596_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3599_ = l_Lean_indentD(v___x_3598_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3597_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v___x_3593_);
v___x_3604_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3605_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
return v___x_3606_;
}
}
else
{
lean_object* v_val_3608_; lean_object* v___x_3610_; 
lean_del_object(v___x_3590_);
lean_dec(v___x_3579_);
lean_dec(v_stx_2326_);
v_val_3608_ = lean_ctor_get(v_fst_3588_, 0);
lean_inc(v_val_3608_);
lean_dec_ref(v_fst_3588_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v_val_3608_);
v___x_3610_ = v___x_3586_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_val_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v___x_3579_);
lean_dec(v_stx_2326_);
v_a_3615_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3583_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3583_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3623_ = l_Lean_Syntax_getArg(v___x_3574_, v___x_3501_);
lean_dec(v___x_3574_);
v___x_3624_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3625_ = l_Lean_Syntax_isOfKind(v___x_3623_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v_env_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3626_ = lean_st_ref_get(v___y_3572_);
v_env_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc_ref(v_env_3627_);
lean_dec(v___x_3626_);
lean_inc_n(v_stx_2326_, 2);
v___x_3628_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3629_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3630_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3629_, v_env_3627_, v___x_3628_);
v___x_3631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3632_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3630_, v___x_3631_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___x_3630_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3663_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3663_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3663_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_fst_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3661_; 
v_fst_3637_ = lean_ctor_get(v_a_3633_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_a_3633_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v_a_3633_, 1);
lean_dec(v_unused_3662_);
v___x_3639_ = v_a_3633_;
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_fst_3637_);
lean_dec(v_a_3633_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3661_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
if (lean_obj_tag(v_fst_3637_) == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
lean_del_object(v___x_3635_);
v___x_3641_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3642_ = l_Lean_MessageData_ofName(v___x_3628_);
lean_inc_ref(v___x_3642_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 7);
lean_ctor_set(v___x_3639_, 1, v___x_3642_);
lean_ctor_set(v___x_3639_, 0, v___x_3641_);
v___x_3644_ = v___x_3639_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3645_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3648_ = l_Lean_indentD(v___x_3647_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3646_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v___x_3642_);
v___x_3653_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3654_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
return v___x_3655_;
}
}
else
{
lean_object* v_val_3657_; lean_object* v___x_3659_; 
lean_del_object(v___x_3639_);
lean_dec(v___x_3628_);
lean_dec(v_stx_2326_);
v_val_3657_ = lean_ctor_get(v_fst_3637_, 0);
lean_inc(v_val_3657_);
lean_dec_ref(v_fst_3637_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_val_3657_);
v___x_3659_ = v___x_3635_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_val_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v___x_3628_);
lean_dec(v_stx_2326_);
v_a_3664_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3632_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3632_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
v___y_3503_ = v___y_3567_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3569_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3571_;
v___y_3508_ = v___y_3572_;
goto v___jp_3502_;
}
}
}
else
{
lean_dec(v___x_3574_);
v___y_3503_ = v___y_3567_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3569_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3571_;
v___y_3508_ = v___y_3572_;
goto v___jp_3502_;
}
}
}
}
else
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3770_ = lean_unsigned_to_nat(0u);
v___x_3771_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3770_);
v___x_3772_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_3771_);
v___x_3773_ = l_Lean_Syntax_isOfKind(v___x_3771_, v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_3771_);
v___x_3775_ = l_Lean_Syntax_isOfKind(v___x_3771_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v_env_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_dec(v___x_3771_);
v___x_3776_ = lean_st_ref_get(v_a_2332_);
v_env_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3777_);
lean_dec(v___x_3776_);
lean_inc_n(v_stx_2326_, 2);
v___x_3778_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3779_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3780_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3779_, v_env_3777_, v___x_3778_);
v___x_3781_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3782_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3780_, v___x_3781_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3780_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3813_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3813_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3813_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v_fst_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3811_; 
v_fst_3787_ = lean_ctor_get(v_a_3783_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_a_3783_, 1);
lean_dec(v_unused_3812_);
v___x_3789_ = v_a_3783_;
v_isShared_3790_ = v_isSharedCheck_3811_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_fst_3787_);
lean_dec(v_a_3783_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3811_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_fst_3787_) == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_del_object(v___x_3785_);
v___x_3791_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3792_ = l_Lean_MessageData_ofName(v___x_3778_);
lean_inc_ref(v___x_3792_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set_tag(v___x_3789_, 7);
lean_ctor_set(v___x_3789_, 1, v___x_3792_);
lean_ctor_set(v___x_3789_, 0, v___x_3791_);
v___x_3794_ = v___x_3789_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3795_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3794_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3798_ = l_Lean_indentD(v___x_3797_);
v___x_3799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3792_);
v___x_3803_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3804_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3805_;
}
}
else
{
lean_object* v_val_3807_; lean_object* v___x_3809_; 
lean_del_object(v___x_3789_);
lean_dec(v___x_3778_);
lean_dec(v_stx_2326_);
v_val_3807_ = lean_ctor_get(v_fst_3787_, 0);
lean_inc(v_val_3807_);
lean_dec_ref(v_fst_3787_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_val_3807_);
v___x_3809_ = v___x_3785_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_val_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v___x_3778_);
lean_dec(v_stx_2326_);
v_a_3814_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3782_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3782_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
lean_dec(v_stx_2326_);
v___x_3822_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2563_, v___x_3771_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3822_;
}
}
else
{
lean_object* v___x_3823_; 
lean_dec(v_stx_2326_);
v___x_3823_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2563_, v___x_3771_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3823_;
}
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3824_);
v___x_3826_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
lean_inc(v___x_3825_);
v___x_3827_ = l_Lean_Syntax_isOfKind(v___x_3825_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
lean_inc(v___x_3825_);
v___x_3829_ = l_Lean_Syntax_isOfKind(v___x_3825_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v_env_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec(v___x_3825_);
v___x_3830_ = lean_st_ref_get(v_a_2332_);
v_env_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc_ref(v_env_3831_);
lean_dec(v___x_3830_);
lean_inc_n(v_stx_2326_, 2);
v___x_3832_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3833_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3834_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3833_, v_env_3831_, v___x_3832_);
v___x_3835_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3836_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3834_, v___x_3835_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3834_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3867_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3867_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3867_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_fst_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3865_; 
v_fst_3841_ = lean_ctor_get(v_a_3837_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3837_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; 
v_unused_3866_ = lean_ctor_get(v_a_3837_, 1);
lean_dec(v_unused_3866_);
v___x_3843_ = v_a_3837_;
v_isShared_3844_ = v_isSharedCheck_3865_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_fst_3841_);
lean_dec(v_a_3837_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3865_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
if (lean_obj_tag(v_fst_3841_) == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
lean_del_object(v___x_3839_);
v___x_3845_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3846_ = l_Lean_MessageData_ofName(v___x_3832_);
lean_inc_ref(v___x_3846_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 7);
lean_ctor_set(v___x_3843_, 1, v___x_3846_);
lean_ctor_set(v___x_3843_, 0, v___x_3845_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3849_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3852_ = l_Lean_indentD(v___x_3851_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3850_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___x_3846_);
v___x_3857_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3858_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3859_;
}
}
else
{
lean_object* v_val_3861_; lean_object* v___x_3863_; 
lean_del_object(v___x_3843_);
lean_dec(v___x_3832_);
lean_dec(v_stx_2326_);
v_val_3861_ = lean_ctor_get(v_fst_3841_, 0);
lean_inc(v_val_3861_);
lean_dec_ref(v_fst_3841_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_val_3861_);
v___x_3863_ = v___x_3839_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_val_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v___x_3832_);
lean_dec(v_stx_2326_);
v_a_3868_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3836_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3836_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec(v_stx_2326_);
v___x_3876_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_3825_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3825_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref(v___x_3876_);
v___x_3878_ = lean_box(0);
v___x_3879_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3877_, v___x_3878_, v___x_3878_, v___x_3878_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3879_;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3876_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3876_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v___x_3888_; 
lean_dec(v_stx_2326_);
v___x_3888_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_3825_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3825_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v___x_3890_ = lean_box(0);
v___x_3891_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_3889_, v___x_3890_, v___x_3890_, v___x_3890_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3891_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_a_3892_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3888_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3888_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3900_);
v___x_3902_ = l_Lean_Syntax_isNone(v___x_3901_);
if (v___x_3902_ == 0)
{
uint8_t v___x_3903_; 
v___x_3903_ = l_Lean_Syntax_matchesNull(v___x_3901_, v___x_3900_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v_env_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3904_ = lean_st_ref_get(v_a_2332_);
v_env_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc_ref(v_env_3905_);
lean_dec(v___x_3904_);
lean_inc_n(v_stx_2326_, 2);
v___x_3906_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3907_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3908_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3907_, v_env_3905_, v___x_3906_);
v___x_3909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3910_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3908_, v___x_3909_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
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
v___x_3920_ = l_Lean_MessageData_ofName(v___x_3906_);
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
v___x_3925_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
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
v___x_3933_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3932_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3933_;
}
}
else
{
lean_object* v_val_3935_; lean_object* v___x_3937_; 
lean_del_object(v___x_3917_);
lean_dec(v___x_3906_);
lean_dec(v_stx_2326_);
v_val_3935_ = lean_ctor_get(v_fst_3915_, 0);
lean_inc(v_val_3935_);
lean_dec_ref(v_fst_3915_);
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
lean_dec(v___x_3906_);
lean_dec(v_stx_2326_);
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
v___y_2581_ = v_a_2327_;
v___y_2582_ = v_a_2328_;
v___y_2583_ = v_a_2329_;
v___y_2584_ = v_a_2330_;
v___y_2585_ = v_a_2331_;
v___y_2586_ = v_a_2332_;
goto v___jp_2580_;
}
}
else
{
lean_dec(v___x_3901_);
v___y_2581_ = v_a_2327_;
v___y_2582_ = v_a_2328_;
v___y_2583_ = v_a_2329_;
v___y_2584_ = v_a_2330_;
v___y_2585_ = v_a_2331_;
v___y_2586_ = v_a_2332_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3950_ = lean_unsigned_to_nat(1u);
v___x_3951_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_3950_);
v___x_3952_ = l_Lean_Syntax_isNone(v___x_3951_);
if (v___x_3952_ == 0)
{
uint8_t v___x_3953_; 
v___x_3953_ = l_Lean_Syntax_matchesNull(v___x_3951_, v___x_3950_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v_env_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3954_ = lean_st_ref_get(v_a_2332_);
v_env_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc_ref(v_env_3955_);
lean_dec(v___x_3954_);
lean_inc_n(v_stx_2326_, 2);
v___x_3956_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_3957_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3958_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3957_, v_env_3955_, v___x_3956_);
v___x_3959_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3960_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_3958_, v___x_3959_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_3958_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3991_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3991_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3991_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v_fst_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3989_; 
v_fst_3965_ = lean_ctor_get(v_a_3961_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_a_3961_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v_a_3961_, 1);
lean_dec(v_unused_3990_);
v___x_3967_ = v_a_3961_;
v_isShared_3968_ = v_isSharedCheck_3989_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_fst_3965_);
lean_dec(v_a_3961_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3989_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
if (lean_obj_tag(v_fst_3965_) == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
lean_del_object(v___x_3963_);
v___x_3969_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_3970_ = l_Lean_MessageData_ofName(v___x_3956_);
lean_inc_ref(v___x_3970_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set_tag(v___x_3967_, 7);
lean_ctor_set(v___x_3967_, 1, v___x_3970_);
lean_ctor_set(v___x_3967_, 0, v___x_3969_);
v___x_3972_ = v___x_3967_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3973_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_3976_ = l_Lean_indentD(v___x_3975_);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3974_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
lean_ctor_set(v___x_3980_, 1, v___x_3970_);
v___x_3981_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3982_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_3983_;
}
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3987_; 
lean_del_object(v___x_3967_);
lean_dec(v___x_3956_);
lean_dec(v_stx_2326_);
v_val_3985_ = lean_ctor_get(v_fst_3965_, 0);
lean_inc(v_val_3985_);
lean_dec_ref(v_fst_3965_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v_val_3985_);
v___x_3987_ = v___x_3963_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_val_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v___x_3956_);
lean_dec(v_stx_2326_);
v_a_3992_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3960_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3960_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
v___y_2380_ = v_a_2327_;
v___y_2381_ = v_a_2328_;
v___y_2382_ = v_a_2329_;
v___y_2383_ = v_a_2330_;
v___y_2384_ = v_a_2331_;
v___y_2385_ = v_a_2332_;
goto v___jp_2379_;
}
}
else
{
lean_dec(v___x_3951_);
v___y_2380_ = v_a_2327_;
v___y_2381_ = v_a_2328_;
v___y_2382_ = v_a_2329_;
v___y_2383_ = v_a_2330_;
v___y_2384_ = v_a_2331_;
v___y_2385_ = v_a_2332_;
goto v___jp_2379_;
}
}
v___jp_2580_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2587_ = lean_unsigned_to_nat(2u);
v___x_2588_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2590_ = l_Lean_Syntax_isOfKind(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v_env_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2591_ = lean_st_ref_get(v___y_2586_);
v_env_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref(v_env_2592_);
lean_dec(v___x_2591_);
lean_inc_n(v_stx_2326_, 2);
v___x_2593_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2594_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2595_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2594_, v_env_2592_, v___x_2593_);
v___x_2596_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2597_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2595_, v___x_2596_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___x_2595_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2628_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2628_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2628_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_fst_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2626_; 
v_fst_2602_ = lean_ctor_get(v_a_2598_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_a_2598_, 1);
lean_dec(v_unused_2627_);
v___x_2604_ = v_a_2598_;
v_isShared_2605_ = v_isSharedCheck_2626_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_fst_2602_);
lean_dec(v_a_2598_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2626_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
if (lean_obj_tag(v_fst_2602_) == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_del_object(v___x_2600_);
v___x_2606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2607_ = l_Lean_MessageData_ofName(v___x_2593_);
lean_inc_ref(v___x_2607_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 7);
lean_ctor_set(v___x_2604_, 1, v___x_2607_);
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2609_ = v___x_2604_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2610_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2613_ = l_Lean_indentD(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2611_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2607_);
v___x_2618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2619_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2620_;
}
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2624_; 
lean_del_object(v___x_2604_);
lean_dec(v___x_2593_);
lean_dec(v_stx_2326_);
v_val_2622_ = lean_ctor_get(v_fst_2602_, 0);
lean_inc(v_val_2622_);
lean_dec_ref(v_fst_2602_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_val_2622_);
v___x_2624_ = v___x_2600_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_val_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v___x_2593_);
lean_dec(v_stx_2326_);
v_a_2629_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2597_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2597_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_unsigned_to_nat(3u);
v___x_2638_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2637_);
lean_dec(v_stx_2326_);
v___x_2639_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2579_, v___x_2638_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2639_;
}
}
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4000_);
v___x_4002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4003_ = l_Lean_Syntax_isOfKind(v___x_4001_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v_env_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4004_ = lean_st_ref_get(v_a_2332_);
v_env_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc_ref(v_env_4005_);
lean_dec(v___x_4004_);
lean_inc_n(v_stx_2326_, 2);
v___x_4006_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4007_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4008_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4007_, v_env_4005_, v___x_4006_);
v___x_4009_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4010_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4008_, v___x_4009_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4008_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4041_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4041_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4041_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_fst_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4039_; 
v_fst_4015_ = lean_ctor_get(v_a_4011_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4039_ == 0)
{
lean_object* v_unused_4040_; 
v_unused_4040_ = lean_ctor_get(v_a_4011_, 1);
lean_dec(v_unused_4040_);
v___x_4017_ = v_a_4011_;
v_isShared_4018_ = v_isSharedCheck_4039_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_fst_4015_);
lean_dec(v_a_4011_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4039_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
if (lean_obj_tag(v_fst_4015_) == 0)
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; 
lean_del_object(v___x_4013_);
v___x_4019_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4020_ = l_Lean_MessageData_ofName(v___x_4006_);
lean_inc_ref(v___x_4020_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set_tag(v___x_4017_, 7);
lean_ctor_set(v___x_4017_, 1, v___x_4020_);
lean_ctor_set(v___x_4017_, 0, v___x_4019_);
v___x_4022_ = v___x_4017_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4023_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4022_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4026_ = l_Lean_indentD(v___x_4025_);
v___x_4027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4024_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4027_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4020_);
v___x_4031_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4032_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4033_;
}
}
else
{
lean_object* v_val_4035_; lean_object* v___x_4037_; 
lean_del_object(v___x_4017_);
lean_dec(v___x_4006_);
lean_dec(v_stx_2326_);
v_val_4035_ = lean_ctor_get(v_fst_4015_, 0);
lean_inc(v_val_4035_);
lean_dec_ref(v_fst_4015_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v_val_4035_);
v___x_4037_ = v___x_4013_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_val_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v___x_4006_);
lean_dec(v_stx_2326_);
v_a_4042_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4010_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4010_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4050_ = lean_unsigned_to_nat(1u);
v___x_4051_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4050_);
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
lean_inc(v___x_4051_);
v___x_4053_ = l_Lean_Syntax_isOfKind(v___x_4051_, v___x_4052_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v_env_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec(v___x_4051_);
v___x_4054_ = lean_st_ref_get(v_a_2332_);
v_env_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc_ref(v_env_4055_);
lean_dec(v___x_4054_);
lean_inc_n(v_stx_2326_, 2);
v___x_4056_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4057_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4058_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4057_, v_env_4055_, v___x_4056_);
v___x_4059_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4060_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4058_, v___x_4059_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4058_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4091_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4091_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4091_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_fst_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4089_; 
v_fst_4065_ = lean_ctor_get(v_a_4061_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_4061_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_a_4061_, 1);
lean_dec(v_unused_4090_);
v___x_4067_ = v_a_4061_;
v_isShared_4068_ = v_isSharedCheck_4089_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_fst_4065_);
lean_dec(v_a_4061_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4089_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
if (lean_obj_tag(v_fst_4065_) == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
lean_del_object(v___x_4063_);
v___x_4069_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4070_ = l_Lean_MessageData_ofName(v___x_4056_);
lean_inc_ref(v___x_4070_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set_tag(v___x_4067_, 7);
lean_ctor_set(v___x_4067_, 1, v___x_4070_);
lean_ctor_set(v___x_4067_, 0, v___x_4069_);
v___x_4072_ = v___x_4067_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4073_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4076_ = l_Lean_indentD(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4074_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4077_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4070_);
v___x_4081_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4082_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4083_;
}
}
else
{
lean_object* v_val_4085_; lean_object* v___x_4087_; 
lean_del_object(v___x_4067_);
lean_dec(v___x_4056_);
lean_dec(v_stx_2326_);
v_val_4085_ = lean_ctor_get(v_fst_4065_, 0);
lean_inc(v_val_4085_);
lean_dec_ref(v_fst_4065_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v_val_4085_);
v___x_4087_ = v___x_4063_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_val_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v___x_4056_);
lean_dec(v_stx_2326_);
v_a_4092_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4060_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4060_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4100_ = l_Lean_Syntax_getArg(v___x_4051_, v___x_4000_);
lean_dec(v___x_4051_);
lean_inc(v___x_4100_);
v___x_4101_ = l_Lean_Syntax_matchesNull(v___x_4100_, v___x_4050_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; lean_object* v_env_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec(v___x_4100_);
v___x_4102_ = lean_st_ref_get(v_a_2332_);
v_env_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc_ref(v_env_4103_);
lean_dec(v___x_4102_);
lean_inc_n(v_stx_2326_, 2);
v___x_4104_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4105_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4106_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4105_, v_env_4103_, v___x_4104_);
v___x_4107_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4108_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4106_, v___x_4107_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4106_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4139_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4139_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v_fst_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4137_; 
v_fst_4113_ = lean_ctor_get(v_a_4109_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_a_4109_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v_a_4109_, 1);
lean_dec(v_unused_4138_);
v___x_4115_ = v_a_4109_;
v_isShared_4116_ = v_isSharedCheck_4137_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_fst_4113_);
lean_dec(v_a_4109_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4137_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
if (lean_obj_tag(v_fst_4113_) == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_del_object(v___x_4111_);
v___x_4117_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4118_ = l_Lean_MessageData_ofName(v___x_4104_);
lean_inc_ref(v___x_4118_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set_tag(v___x_4115_, 7);
lean_ctor_set(v___x_4115_, 1, v___x_4118_);
lean_ctor_set(v___x_4115_, 0, v___x_4117_);
v___x_4120_ = v___x_4115_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4121_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4124_ = l_Lean_indentD(v___x_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4122_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v___x_4118_);
v___x_4129_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4130_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4131_;
}
}
else
{
lean_object* v_val_4133_; lean_object* v___x_4135_; 
lean_del_object(v___x_4115_);
lean_dec(v___x_4104_);
lean_dec(v_stx_2326_);
v_val_4133_ = lean_ctor_get(v_fst_4113_, 0);
lean_inc(v_val_4133_);
lean_dec_ref(v_fst_4113_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v_val_4133_);
v___x_4135_ = v___x_4111_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_val_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v___x_4104_);
lean_dec(v_stx_2326_);
v_a_4140_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4108_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4108_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
v___x_4148_ = l_Lean_Syntax_getArg(v___x_4100_, v___x_4000_);
lean_dec(v___x_4100_);
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4150_ = l_Lean_Syntax_isOfKind(v___x_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v_env_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4151_ = lean_st_ref_get(v_a_2332_);
v_env_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc_ref(v_env_4152_);
lean_dec(v___x_4151_);
lean_inc_n(v_stx_2326_, 2);
v___x_4153_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4154_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4155_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4154_, v_env_4152_, v___x_4153_);
v___x_4156_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4157_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4155_, v___x_4156_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4155_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4188_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4188_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4188_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v_fst_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4186_; 
v_fst_4162_ = lean_ctor_get(v_a_4158_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_a_4158_);
if (v_isSharedCheck_4186_ == 0)
{
lean_object* v_unused_4187_; 
v_unused_4187_ = lean_ctor_get(v_a_4158_, 1);
lean_dec(v_unused_4187_);
v___x_4164_ = v_a_4158_;
v_isShared_4165_ = v_isSharedCheck_4186_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_fst_4162_);
lean_dec(v_a_4158_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4186_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
if (lean_obj_tag(v_fst_4162_) == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
lean_del_object(v___x_4160_);
v___x_4166_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4167_ = l_Lean_MessageData_ofName(v___x_4153_);
lean_inc_ref(v___x_4167_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set_tag(v___x_4164_, 7);
lean_ctor_set(v___x_4164_, 1, v___x_4167_);
lean_ctor_set(v___x_4164_, 0, v___x_4166_);
v___x_4169_ = v___x_4164_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4170_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4173_ = l_Lean_indentD(v___x_4172_);
v___x_4174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4171_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4174_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___x_4167_);
v___x_4178_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4179_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4180_;
}
}
else
{
lean_object* v_val_4182_; lean_object* v___x_4184_; 
lean_del_object(v___x_4164_);
lean_dec(v___x_4153_);
lean_dec(v_stx_2326_);
v_val_4182_ = lean_ctor_get(v_fst_4162_, 0);
lean_inc(v_val_4182_);
lean_dec_ref(v_fst_4162_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v_val_4182_);
v___x_4184_ = v___x_4160_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_val_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec(v___x_4153_);
lean_dec(v_stx_2326_);
v_a_4189_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4157_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4157_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
lean_dec(v_stx_2326_);
v___x_4197_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
return v___x_4198_;
}
}
}
}
}
}
else
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4199_);
v___x_4201_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_4202_ = l_Lean_Syntax_isOfKind(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v_env_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4203_ = lean_st_ref_get(v_a_2332_);
v_env_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc_ref(v_env_4204_);
lean_dec(v___x_4203_);
lean_inc_n(v_stx_2326_, 2);
v___x_4205_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4206_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4207_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4206_, v_env_4204_, v___x_4205_);
v___x_4208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4209_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4207_, v___x_4208_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4207_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4240_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4240_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4240_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v_fst_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4238_; 
v_fst_4214_ = lean_ctor_get(v_a_4210_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_a_4210_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v_a_4210_, 1);
lean_dec(v_unused_4239_);
v___x_4216_ = v_a_4210_;
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_fst_4214_);
lean_dec(v_a_4210_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
if (lean_obj_tag(v_fst_4214_) == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_del_object(v___x_4212_);
v___x_4218_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4219_ = l_Lean_MessageData_ofName(v___x_4205_);
lean_inc_ref(v___x_4219_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set_tag(v___x_4216_, 7);
lean_ctor_set(v___x_4216_, 1, v___x_4219_);
lean_ctor_set(v___x_4216_, 0, v___x_4218_);
v___x_4221_ = v___x_4216_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4233_, 1, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4222_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4221_);
lean_ctor_set(v___x_4223_, 1, v___x_4222_);
v___x_4224_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4225_ = l_Lean_indentD(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4223_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4226_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
lean_ctor_set(v___x_4229_, 1, v___x_4219_);
v___x_4230_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4231_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4232_;
}
}
else
{
lean_object* v_val_4234_; lean_object* v___x_4236_; 
lean_del_object(v___x_4216_);
lean_dec(v___x_4205_);
lean_dec(v_stx_2326_);
v_val_4234_ = lean_ctor_get(v_fst_4214_, 0);
lean_inc(v_val_4234_);
lean_dec_ref(v_fst_4214_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v_val_4234_);
v___x_4236_ = v___x_4212_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_val_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec(v___x_4205_);
lean_dec(v_stx_2326_);
v_a_4241_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4209_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4209_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4249_ = lean_unsigned_to_nat(2u);
v___x_4250_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4249_);
v___x_4251_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_4252_ = l_Lean_Syntax_isOfKind(v___x_4250_, v___x_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v_env_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4253_ = lean_st_ref_get(v_a_2332_);
v_env_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc_ref(v_env_4254_);
lean_dec(v___x_4253_);
lean_inc_n(v_stx_2326_, 2);
v___x_4255_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4256_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4257_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4256_, v_env_4254_, v___x_4255_);
v___x_4258_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4259_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4257_, v___x_4258_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4257_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4290_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4290_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4290_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v_fst_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4288_; 
v_fst_4264_ = lean_ctor_get(v_a_4260_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_a_4260_);
if (v_isSharedCheck_4288_ == 0)
{
lean_object* v_unused_4289_; 
v_unused_4289_ = lean_ctor_get(v_a_4260_, 1);
lean_dec(v_unused_4289_);
v___x_4266_ = v_a_4260_;
v_isShared_4267_ = v_isSharedCheck_4288_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_fst_4264_);
lean_dec(v_a_4260_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4288_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
if (lean_obj_tag(v_fst_4264_) == 0)
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
lean_del_object(v___x_4262_);
v___x_4268_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4269_ = l_Lean_MessageData_ofName(v___x_4255_);
lean_inc_ref(v___x_4269_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 7);
lean_ctor_set(v___x_4266_, 1, v___x_4269_);
lean_ctor_set(v___x_4266_, 0, v___x_4268_);
v___x_4271_ = v___x_4266_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4272_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4275_ = l_Lean_indentD(v___x_4274_);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4273_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
lean_ctor_set(v___x_4279_, 1, v___x_4269_);
v___x_4280_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4281_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4282_;
}
}
else
{
lean_object* v_val_4284_; lean_object* v___x_4286_; 
lean_del_object(v___x_4266_);
lean_dec(v___x_4255_);
lean_dec(v_stx_2326_);
v_val_4284_ = lean_ctor_get(v_fst_4264_, 0);
lean_inc(v_val_4284_);
lean_dec_ref(v_fst_4264_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v_val_4284_);
v___x_4286_ = v___x_4262_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_val_4284_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v___x_4255_);
lean_dec(v_stx_2326_);
v_a_4291_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4259_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4259_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_dec(v_stx_2326_);
v___x_4299_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4299_);
return v___x_4300_;
}
}
}
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; 
v___x_4301_ = lean_unsigned_to_nat(1u);
v___x_4302_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4301_);
v___x_4303_ = l_Lean_Syntax_isNone(v___x_4302_);
if (v___x_4303_ == 0)
{
uint8_t v___x_4304_; 
v___x_4304_ = l_Lean_Syntax_matchesNull(v___x_4302_, v___x_4301_);
if (v___x_4304_ == 0)
{
lean_object* v___x_4305_; lean_object* v_env_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
lean_del_object(v___x_2363_);
v___x_4305_ = lean_st_ref_get(v_a_2332_);
v_env_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc_ref(v_env_4306_);
lean_dec(v___x_4305_);
lean_inc_n(v_stx_2326_, 2);
v___x_4307_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4308_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4309_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4308_, v_env_4306_, v___x_4307_);
v___x_4310_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4311_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4309_, v___x_4310_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4309_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4342_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4342_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4342_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_fst_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4340_; 
v_fst_4316_ = lean_ctor_get(v_a_4312_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_a_4312_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; 
v_unused_4341_ = lean_ctor_get(v_a_4312_, 1);
lean_dec(v_unused_4341_);
v___x_4318_ = v_a_4312_;
v_isShared_4319_ = v_isSharedCheck_4340_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_fst_4316_);
lean_dec(v_a_4312_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4340_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
if (lean_obj_tag(v_fst_4316_) == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
lean_del_object(v___x_4314_);
v___x_4320_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4321_ = l_Lean_MessageData_ofName(v___x_4307_);
lean_inc_ref(v___x_4321_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 7);
lean_ctor_set(v___x_4318_, 1, v___x_4321_);
lean_ctor_set(v___x_4318_, 0, v___x_4320_);
v___x_4323_ = v___x_4318_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4324_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4323_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4327_ = l_Lean_indentD(v___x_4326_);
v___x_4328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4325_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4328_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
lean_ctor_set(v___x_4331_, 1, v___x_4321_);
v___x_4332_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4333_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4334_;
}
}
else
{
lean_object* v_val_4336_; lean_object* v___x_4338_; 
lean_del_object(v___x_4318_);
lean_dec(v___x_4307_);
lean_dec(v_stx_2326_);
v_val_4336_ = lean_ctor_get(v_fst_4316_, 0);
lean_inc(v_val_4336_);
lean_dec_ref(v_fst_4316_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v_val_4336_);
v___x_4338_ = v___x_4314_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_val_4336_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v___x_4307_);
lean_dec(v_stx_2326_);
v_a_4343_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4311_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4311_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
v___y_2451_ = v_a_2327_;
v___y_2452_ = v_a_2328_;
v___y_2453_ = v_a_2329_;
v___y_2454_ = v_a_2330_;
v___y_2455_ = v_a_2331_;
v___y_2456_ = v_a_2332_;
goto v___jp_2450_;
}
}
else
{
lean_dec(v___x_4302_);
v___y_2451_ = v_a_2327_;
v___y_2452_ = v_a_2328_;
v___y_2453_ = v_a_2329_;
v___y_2454_ = v_a_2330_;
v___y_2455_ = v_a_2331_;
v___y_2456_ = v_a_2332_;
goto v___jp_2450_;
}
}
}
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_del_object(v___x_2363_);
v___x_4351_ = lean_unsigned_to_nat(1u);
v___x_4352_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4351_);
lean_dec(v_stx_2326_);
v___x_4353_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4352_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4353_;
}
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_del_object(v___x_2363_);
lean_dec(v_stx_2326_);
v___x_4354_ = lean_unsigned_to_nat(1u);
v___x_4355_ = l_Lean_NameSet_empty;
v___x_4356_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
lean_ctor_set_uint8(v___x_4356_, sizeof(void*)*2, v___x_2567_);
lean_ctor_set_uint8(v___x_4356_, sizeof(void*)*2 + 1, v___x_2567_);
lean_ctor_set_uint8(v___x_4356_, sizeof(void*)*2 + 2, v___x_2567_);
lean_ctor_set_uint8(v___x_4356_, sizeof(void*)*2 + 3, v___x_2567_);
v___x_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
return v___x_4357_;
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
lean_del_object(v___x_2363_);
v___x_4358_ = lean_unsigned_to_nat(0u);
v___x_4363_ = lean_unsigned_to_nat(1u);
v___x_4364_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_4363_);
v___x_4365_ = l_Lean_Syntax_isNone(v___x_4364_);
if (v___x_4365_ == 0)
{
uint8_t v___x_4366_; 
v___x_4366_ = l_Lean_Syntax_matchesNull(v___x_4364_, v___x_4363_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; lean_object* v_env_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4367_ = lean_st_ref_get(v_a_2332_);
v_env_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc_ref(v_env_4368_);
lean_dec(v___x_4367_);
lean_inc_n(v_stx_2326_, 2);
v___x_4369_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_4370_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4371_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4370_, v_env_4368_, v___x_4369_);
v___x_4372_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4373_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_4371_, v___x_4372_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v___x_4371_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4404_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4404_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4404_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v_fst_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4402_; 
v_fst_4378_ = lean_ctor_get(v_a_4374_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_a_4374_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v_a_4374_, 1);
lean_dec(v_unused_4403_);
v___x_4380_ = v_a_4374_;
v_isShared_4381_ = v_isSharedCheck_4402_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_fst_4378_);
lean_dec(v_a_4374_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4402_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
if (lean_obj_tag(v_fst_4378_) == 0)
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
lean_del_object(v___x_4376_);
v___x_4382_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_4383_ = l_Lean_MessageData_ofName(v___x_4369_);
lean_inc_ref(v___x_4383_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 7);
lean_ctor_set(v___x_4380_, 1, v___x_4383_);
lean_ctor_set(v___x_4380_, 0, v___x_4382_);
v___x_4385_ = v___x_4380_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_4389_ = l_Lean_indentD(v___x_4388_);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4387_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
lean_ctor_set(v___x_4393_, 1, v___x_4383_);
v___x_4394_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4395_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
return v___x_4396_;
}
}
else
{
lean_object* v_val_4398_; lean_object* v___x_4400_; 
lean_del_object(v___x_4380_);
lean_dec(v___x_4369_);
lean_dec(v_stx_2326_);
v_val_4398_ = lean_ctor_get(v_fst_4378_, 0);
lean_inc(v_val_4398_);
lean_dec_ref(v_fst_4378_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v_val_4398_);
v___x_4400_ = v___x_4376_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_val_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
lean_dec(v___x_4369_);
lean_dec(v_stx_2326_);
v_a_4405_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4373_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4373_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
else
{
lean_dec(v_stx_2326_);
goto v___jp_4359_;
}
}
else
{
lean_dec(v___x_4364_);
lean_dec(v_stx_2326_);
goto v___jp_4359_;
}
v___jp_4359_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = l_Lean_NameSet_empty;
v___x_4361_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4361_, 0, v___x_4358_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*2, v___x_2565_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*2 + 1, v___x_2565_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*2 + 2, v___x_2563_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*2 + 3, v___x_2563_);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
}
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
lean_del_object(v___x_2363_);
lean_dec(v_stx_2326_);
v___x_4413_ = lean_unsigned_to_nat(0u);
v___x_4414_ = l_Lean_NameSet_empty;
v___x_4415_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4415_, 0, v___x_4413_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*2, v___x_2562_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*2 + 1, v___x_2563_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*2 + 2, v___x_2562_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*2 + 3, v___x_2563_);
v___x_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
return v___x_4416_;
}
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_del_object(v___x_2363_);
lean_dec(v_stx_2326_);
v___x_4417_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83);
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
return v___x_4418_;
}
v___jp_2379_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2386_ = lean_unsigned_to_nat(2u);
v___x_2387_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2389_ = l_Lean_Syntax_isOfKind(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v_env_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2390_ = lean_st_ref_get(v___y_2385_);
v_env_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc_ref(v_env_2391_);
lean_dec(v___x_2390_);
lean_inc_n(v_stx_2326_, 2);
v___x_2392_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2393_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2394_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2393_, v_env_2391_, v___x_2392_);
v___x_2395_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2396_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2394_, v___x_2395_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2427_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2427_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2427_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_fst_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2425_; 
v_fst_2401_ = lean_ctor_get(v_a_2397_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_a_2397_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v_a_2397_, 1);
lean_dec(v_unused_2426_);
v___x_2403_ = v_a_2397_;
v_isShared_2404_ = v_isSharedCheck_2425_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_fst_2401_);
lean_dec(v_a_2397_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2425_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
if (lean_obj_tag(v_fst_2401_) == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_del_object(v___x_2399_);
v___x_2405_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2406_ = l_Lean_MessageData_ofName(v___x_2392_);
lean_inc_ref(v___x_2406_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 7);
lean_ctor_set(v___x_2403_, 1, v___x_2406_);
lean_ctor_set(v___x_2403_, 0, v___x_2405_);
v___x_2408_ = v___x_2403_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2409_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2412_ = l_Lean_indentD(v___x_2411_);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2406_);
v___x_2417_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2418_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2419_;
}
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; 
lean_del_object(v___x_2403_);
lean_dec(v___x_2392_);
lean_dec(v_stx_2326_);
v_val_2421_ = lean_ctor_get(v_fst_2401_, 0);
lean_inc(v_val_2421_);
lean_dec_ref(v_fst_2401_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_val_2421_);
v___x_2423_ = v___x_2399_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_val_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v___x_2392_);
lean_dec(v_stx_2326_);
v_a_2428_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2396_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2396_);
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
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2436_ = lean_unsigned_to_nat(7u);
v___x_2437_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2436_);
v___x_2438_ = lean_unsigned_to_nat(8u);
v___x_2439_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2438_);
lean_dec(v_stx_2326_);
v___x_2440_ = l_Lean_Syntax_getOptional_x3f(v___x_2439_);
lean_dec(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_box(0);
v___y_2335_ = v___y_2384_;
v___y_2336_ = v___y_2381_;
v___y_2337_ = v___y_2382_;
v___y_2338_ = v___y_2380_;
v___y_2339_ = v___y_2385_;
v___y_2340_ = v___y_2383_;
v___y_2341_ = v___x_2437_;
v___y_2342_ = v___x_2441_;
goto v___jp_2334_;
}
else
{
lean_object* v_val_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
v_val_2442_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2440_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_val_2442_);
lean_dec(v___x_2440_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_val_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
v___y_2335_ = v___y_2384_;
v___y_2336_ = v___y_2381_;
v___y_2337_ = v___y_2382_;
v___y_2338_ = v___y_2380_;
v___y_2339_ = v___y_2385_;
v___y_2340_ = v___y_2383_;
v___y_2341_ = v___x_2437_;
v___y_2342_ = v___x_2447_;
goto v___jp_2334_;
}
}
}
}
}
v___jp_2450_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2457_ = lean_unsigned_to_nat(2u);
v___x_2458_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
v___x_2460_ = l_Lean_Syntax_isOfKind(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v_env_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_del_object(v___x_2363_);
v___x_2461_ = lean_st_ref_get(v___y_2456_);
v_env_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc_ref(v_env_2462_);
lean_dec(v___x_2461_);
lean_inc_n(v_stx_2326_, 2);
v___x_2463_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2464_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2465_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2464_, v_env_2462_, v___x_2463_);
v___x_2466_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2467_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2465_, v___x_2466_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___x_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2498_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2498_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2498_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_fst_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2496_; 
v_fst_2472_ = lean_ctor_get(v_a_2468_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_a_2468_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v_a_2468_, 1);
lean_dec(v_unused_2497_);
v___x_2474_ = v_a_2468_;
v_isShared_2475_ = v_isSharedCheck_2496_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_fst_2472_);
lean_dec(v_a_2468_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2496_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
if (lean_obj_tag(v_fst_2472_) == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_del_object(v___x_2470_);
v___x_2476_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2477_ = l_Lean_MessageData_ofName(v___x_2463_);
lean_inc_ref(v___x_2477_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 7);
lean_ctor_set(v___x_2474_, 1, v___x_2477_);
lean_ctor_set(v___x_2474_, 0, v___x_2476_);
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2480_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2483_ = l_Lean_indentD(v___x_2482_);
v___x_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2481_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2477_);
v___x_2488_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2489_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2490_;
}
}
else
{
lean_object* v_val_2492_; lean_object* v___x_2494_; 
lean_del_object(v___x_2474_);
lean_dec(v___x_2463_);
lean_dec(v_stx_2326_);
v_val_2492_ = lean_ctor_get(v_fst_2472_, 0);
lean_inc(v_val_2492_);
lean_dec_ref(v_fst_2472_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v_val_2492_);
v___x_2494_ = v___x_2470_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_val_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v___x_2463_);
lean_dec(v_stx_2326_);
v_a_2499_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2467_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2467_);
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
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2507_ = lean_unsigned_to_nat(3u);
v___x_2508_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2510_ = l_Lean_Syntax_isOfKind(v___x_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v_env_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_del_object(v___x_2363_);
v___x_2511_ = lean_st_ref_get(v___y_2456_);
v_env_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_ref(v_env_2512_);
lean_dec(v___x_2511_);
lean_inc_n(v_stx_2326_, 2);
v___x_2513_ = l_Lean_Syntax_getKind(v_stx_2326_);
v___x_2514_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2515_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2514_, v_env_2512_, v___x_2513_);
v___x_2516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2517_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2326_, v___x_2515_, v___x_2516_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___x_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2548_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2548_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2548_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_fst_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2546_; 
v_fst_2522_ = lean_ctor_get(v_a_2518_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v_a_2518_, 1);
lean_dec(v_unused_2547_);
v___x_2524_ = v_a_2518_;
v_isShared_2525_ = v_isSharedCheck_2546_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_fst_2522_);
lean_dec(v_a_2518_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2546_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
if (lean_obj_tag(v_fst_2522_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_del_object(v___x_2520_);
v___x_2526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
v___x_2527_ = l_Lean_MessageData_ofName(v___x_2513_);
lean_inc_ref(v___x_2527_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 7);
lean_ctor_set(v___x_2524_, 1, v___x_2527_);
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2530_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2533_ = l_Lean_indentD(v___x_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2527_);
v___x_2538_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2539_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2540_;
}
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2544_; 
lean_del_object(v___x_2524_);
lean_dec(v___x_2513_);
lean_dec(v_stx_2326_);
v_val_2542_ = lean_ctor_get(v_fst_2522_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v_fst_2522_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_val_2542_);
v___x_2544_ = v___x_2520_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_val_2542_);
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
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v___x_2513_);
lean_dec(v_stx_2326_);
v_a_2549_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2517_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2517_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_dec(v_stx_2326_);
v___x_2557_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2557_);
v___x_2559_ = v___x_2363_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec(v_stx_2326_);
v_a_4420_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_2360_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_2360_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
v___jp_2334_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2343_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___y_2341_);
v___x_2346_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2343_, v___x_2344_, v___x_2345_, v___y_2342_, v___y_2338_, v___y_2336_, v___y_2337_, v___y_2340_, v___y_2335_, v___y_2339_);
return v___x_2346_;
}
v___jp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2348_, v_bodyInfo_2349_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
v___jp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2353_, v_bodyInfo_2354_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4428_, size_t v_sz_4429_, size_t v_i_4430_, lean_object* v_b_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
uint8_t v___x_4439_; 
v___x_4439_ = lean_usize_dec_lt(v_i_4430_, v_sz_4429_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v_b_4431_);
return v___x_4440_;
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4442_; 
v_a_4441_ = lean_array_uget_borrowed(v_as_4428_, v_i_4430_);
lean_inc(v_a_4441_);
v___x_4442_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4441_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; size_t v___x_4445_; size_t v___x_4446_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref(v___x_4442_);
v___x_4444_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_4431_, v_a_4443_);
v___x_4445_ = ((size_t)1ULL);
v___x_4446_ = lean_usize_add(v_i_4430_, v___x_4445_);
v_i_4430_ = v___x_4446_;
v_b_4431_ = v___x_4444_;
goto _start;
}
else
{
lean_dec_ref(v_b_4431_);
return v___x_4442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_info_4456_; lean_object* v___x_4457_; size_t v_sz_4458_; size_t v___x_4459_; lean_object* v___x_4460_; 
v_info_4456_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4457_ = l_Lean_Parser_Term_getDoElems(v_stx_4448_);
v_sz_4458_ = lean_array_size(v___x_4457_);
v___x_4459_ = ((size_t)0ULL);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4457_, v_sz_4458_, v___x_4459_, v_info_4456_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec_ref(v___x_4457_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4479_, lean_object* v_sz_4480_, lean_object* v_i_4481_, lean_object* v_b_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
size_t v_sz_boxed_4490_; size_t v_i_boxed_4491_; lean_object* v_res_4492_; 
v_sz_boxed_4490_ = lean_unbox_usize(v_sz_4480_);
lean_dec(v_sz_4480_);
v_i_boxed_4491_ = lean_unbox_usize(v_i_4481_);
lean_dec(v_i_4481_);
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4479_, v_sz_boxed_4490_, v_i_boxed_4491_, v_b_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec_ref(v_as_4479_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4493_, lean_object* v_sz_4494_, lean_object* v_i_4495_, lean_object* v_b_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
size_t v_sz_boxed_4504_; size_t v_i_boxed_4505_; lean_object* v_res_4506_; 
v_sz_boxed_4504_ = lean_unbox_usize(v_sz_4494_);
lean_dec(v_sz_4494_);
v_i_boxed_4505_ = lean_unbox_usize(v_i_4495_);
lean_dec(v_i_4495_);
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4493_, v_sz_boxed_4504_, v_i_boxed_4505_, v_b_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v_as_4493_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_4507_, lean_object* v_rhs_x3f_4508_, lean_object* v_otherwise_x3f_4509_, lean_object* v_body_x3f_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_4507_, v_rhs_x3f_4508_, v_otherwise_x3f_4509_, v_body_x3f_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4519_, lean_object* v_as_4520_, lean_object* v_sz_4521_, lean_object* v_i_4522_, lean_object* v_b_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
uint8_t v___x_283569__boxed_4531_; size_t v_sz_boxed_4532_; size_t v_i_boxed_4533_; lean_object* v_res_4534_; 
v___x_283569__boxed_4531_ = lean_unbox(v___x_4519_);
v_sz_boxed_4532_ = lean_unbox_usize(v_sz_4521_);
lean_dec(v_sz_4521_);
v_i_boxed_4533_ = lean_unbox_usize(v_i_4522_);
lean_dec(v_i_4522_);
v_res_4534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_283569__boxed_4531_, v_as_4520_, v_sz_boxed_4532_, v_i_boxed_4533_, v_b_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec_ref(v_as_4520_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4535_, lean_object* v_as_4536_, lean_object* v_sz_4537_, lean_object* v_i_4538_, lean_object* v_b_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v___x_283620__boxed_4547_; size_t v_sz_boxed_4548_; size_t v_i_boxed_4549_; lean_object* v_res_4550_; 
v___x_283620__boxed_4547_ = lean_unbox(v___x_4535_);
v_sz_boxed_4548_ = lean_unbox_usize(v_sz_4537_);
lean_dec(v_sz_4537_);
v_i_boxed_4549_ = lean_unbox_usize(v_i_4538_);
lean_dec(v_i_4538_);
v_res_4550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_283620__boxed_4547_, v_as_4536_, v_sz_boxed_4548_, v_i_boxed_4549_, v_b_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec_ref(v_as_4536_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_4551_, lean_object* v_sz_4552_, lean_object* v_i_4553_, lean_object* v_b_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
size_t v_sz_boxed_4562_; size_t v_i_boxed_4563_; lean_object* v_res_4564_; 
v_sz_boxed_4562_ = lean_unbox_usize(v_sz_4552_);
lean_dec(v_sz_4552_);
v_i_boxed_4563_ = lean_unbox_usize(v_i_4553_);
lean_dec(v_i_4553_);
v_res_4564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_4551_, v_sz_boxed_4562_, v_i_boxed_4563_, v_b_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec_ref(v_as_4551_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_4565_, lean_object* v_decl_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
uint8_t v_reassignment_boxed_4574_; lean_object* v_res_4575_; 
v_reassignment_boxed_4574_ = lean_unbox(v_reassignment_4565_);
v_res_4575_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_4574_, v_decl_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* v_00_u03b1_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_00_u03b1_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_00_u03b1_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_4603_, lean_object* v_ref_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v___x_4612_; 
v___x_4612_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_4604_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_4613_, lean_object* v_ref_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_4613_, v_ref_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_4623_, lean_object* v_x_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_4633_, lean_object* v_x_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_4633_, v_x_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_4643_, lean_object* v_as_4644_, lean_object* v_as_x27_4645_, lean_object* v_b_4646_, lean_object* v_a_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_4643_, v_as_x27_4645_, v_b_4646_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_4656_, lean_object* v_as_4657_, lean_object* v_as_x27_4658_, lean_object* v_b_4659_, lean_object* v_a_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_4656_, v_as_4657_, v_as_x27_4658_, v_b_4659_, v_a_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v_as_x27_4658_);
lean_dec(v_as_4657_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_4669_, lean_object* v_msg_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_4679_, lean_object* v_msg_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_4679_, v_msg_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_4689_, lean_object* v_msg_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_4689_, v_msg_4690_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_4699_, lean_object* v_msg_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_4699_, v_msg_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_4709_, lean_object* v_as_x27_4710_, lean_object* v_b_4711_, lean_object* v_a_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_4710_, v_b_4711_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_4721_, lean_object* v_as_x27_4722_, lean_object* v_b_4723_, lean_object* v_a_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_4721_, v_as_x27_4722_, v_b_4723_, v_a_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v_as_x27_4722_);
lean_dec(v_as_4721_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_4733_, lean_object* v_ref_4734_, lean_object* v_msg_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_4734_, v_msg_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_4744_, lean_object* v_ref_4745_, lean_object* v_msg_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_4744_, v_ref_4745_, v_msg_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v_ref_4745_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_4755_, lean_object* v_macroStack_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_4755_, v_macroStack_4756_, v___y_4761_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_4765_, lean_object* v_macroStack_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_4765_, v_macroStack_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_4775_, lean_object* v_m_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_4776_, v_a_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_4779_, lean_object* v_m_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_4779_, v_m_4780_, v_a_4781_);
lean_dec(v_a_4781_);
lean_dec_ref(v_m_4780_);
return v_res_4782_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_4783_, lean_object* v_x_4784_, lean_object* v_x_4785_){
_start:
{
uint8_t v___x_4786_; 
v___x_4786_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_4784_, v_x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_4787_, lean_object* v_x_4788_, lean_object* v_x_4789_){
_start:
{
uint8_t v_res_4790_; lean_object* v_r_4791_; 
v_res_4790_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_4787_, v_x_4788_, v_x_4789_);
lean_dec_ref(v_x_4789_);
lean_dec_ref(v_x_4788_);
v_r_4791_ = lean_box(v_res_4790_);
return v_r_4791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_4792_, lean_object* v_a_4793_, lean_object* v_x_4794_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_4793_, v_x_4794_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_4796_, lean_object* v_a_4797_, lean_object* v_x_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_4796_, v_a_4797_, v_x_4798_);
lean_dec(v_x_4798_);
lean_dec(v_a_4797_);
return v_res_4799_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_4800_, lean_object* v_x_4801_, size_t v_x_4802_, lean_object* v_x_4803_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_4801_, v_x_4802_, v_x_4803_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4805_, lean_object* v_x_4806_, lean_object* v_x_4807_, lean_object* v_x_4808_){
_start:
{
size_t v_x_289343__boxed_4809_; uint8_t v_res_4810_; lean_object* v_r_4811_; 
v_x_289343__boxed_4809_ = lean_unbox_usize(v_x_4807_);
lean_dec(v_x_4807_);
v_res_4810_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_4805_, v_x_4806_, v_x_289343__boxed_4809_, v_x_4808_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4806_);
v_r_4811_ = lean_box(v_res_4810_);
return v_r_4811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_4812_, lean_object* v_keys_4813_, lean_object* v_vals_4814_, lean_object* v_heq_4815_, lean_object* v_i_4816_, lean_object* v_k_4817_){
_start:
{
uint8_t v___x_4818_; 
v___x_4818_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_4813_, v_i_4816_, v_k_4817_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_4819_, lean_object* v_keys_4820_, lean_object* v_vals_4821_, lean_object* v_heq_4822_, lean_object* v_i_4823_, lean_object* v_k_4824_){
_start:
{
uint8_t v_res_4825_; lean_object* v_r_4826_; 
v_res_4825_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_4819_, v_keys_4820_, v_vals_4821_, v_heq_4822_, v_i_4823_, v_k_4824_);
lean_dec_ref(v_k_4824_);
lean_dec_ref(v_vals_4821_);
lean_dec_ref(v_keys_4820_);
v_r_4826_ = lean_box(v_res_4825_);
return v_r_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
return v_res_4862_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin);
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
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
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
