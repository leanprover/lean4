// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndInfo
// Imports: public import Lean.Meta.Basic public import Lean.ReservedNameAction
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqFunIndParamKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqFunIndParamKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqFunIndParamKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqFunIndParamKind___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqFunIndParamKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqFunIndParamKind = (const lean_object*)&l_Lean_Meta_instBEqFunIndParamKind___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.FunIndParamKind.dropped"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.FunIndParamKind.param"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.FunIndParamKind.target"};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprFunIndParamKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprFunIndParamKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprFunIndParamKind___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprFunIndParamKind = (const lean_object*)&l_Lean_Meta_instReprFunIndParamKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind;
static const lean_array_object l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value),((lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedFunIndInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedFunIndInfo = (const lean_object*)&l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprFunIndInfo_repr_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "funName"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "funIndName"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "levelMask"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16;
static const lean_string_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprFunIndInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprFunIndInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprFunIndInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprFunIndInfo = (const lean_object*)&l_Lean_Meta_instReprFunIndInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "funIndInfoExt"};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 166, 99, 175, 176, 185, 8, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_funIndInfoExt;
static const lean_string_object l_Lean_Meta_getFunInductName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l_Lean_Meta_getFunInductName___closed__0 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getFunInductName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunInductName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 227, 157, 243, 169, 45, 185, 145)}};
static const lean_object* l_Lean_Meta_getFunInductName___closed__1 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__1_value;
static const lean_string_object l_Lean_Meta_getFunInductName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "induct_unfolding"};
static const lean_object* l_Lean_Meta_getFunInductName___closed__2 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getFunInductName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunInductName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 44, 9, 205, 255, 228, 185, 244)}};
static const lean_object* l_Lean_Meta_getFunInductName___closed__3 = (const lean_object*)&l_Lean_Meta_getFunInductName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getFunCasesName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fun_cases"};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__0 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getFunCasesName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunCasesName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 179, 52, 186, 51, 24, 50, 193)}};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__1 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__1_value;
static const lean_string_object l_Lean_Meta_getFunCasesName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fun_cases_unfolding"};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__2 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getFunCasesName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getFunCasesName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 243, 0, 15, 80, 212, 101, 186)}};
static const lean_object* l_Lean_Meta_getFunCasesName___closed__3 = (const lean_object*)&l_Lean_Meta_getFunCasesName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getMutualInductName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mutual_induct"};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__0 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getMutualInductName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getMutualInductName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 83, 25, 196, 5, 111, 46, 167)}};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__1 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__1_value;
static const lean_string_object l_Lean_Meta_getMutualInductName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "mutual_induct_unfolding"};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__2 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__2_value;
static const lean_ctor_object l_Lean_Meta_getMutualInductName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getMutualInductName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 58, 37, 55, 35, 7, 46, 118)}};
static const lean_object* l_Lean_Meta_getMutualInductName___closed__3 = (const lean_object*)&l_Lean_Meta_getMutualInductName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__0;
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__1;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Tactic.FunIndInfo"};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__2 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__2_value;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.setFunIndInfo"};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__3 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__3_value;
static const lean_string_object l_Lean_Meta_setFunIndInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 144, .m_capacity = 144, .m_length = 143, .m_data = "assertion violation: !(funIndInfoExt.contains ( __do_lift._@.Lean.Meta.Tactic.FunIndInfo.992483078._hygCtx._hyg.9.0 ) funIndInfo.funIndName)\n  "};
static const lean_object* l_Lean_Meta_setFunIndInfo___closed__4 = (const lean_object*)&l_Lean_Meta_setFunIndInfo___closed__4_value;
static lean_once_cell_t l_Lean_Meta_setFunIndInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_FunIndParamKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_FunIndParamKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_FunIndParamKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(lean_object* v_dropped_22_){
_start:
{
lean_inc(v_dropped_22_);
return v_dropped_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___redArg___boxed(lean_object* v_dropped_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(v_dropped_23_);
lean_dec(v_dropped_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_dropped_28_){
_start:
{
lean_inc(v_dropped_28_);
return v_dropped_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_dropped_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_dropped_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_FunIndParamKind_dropped_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_dropped_32_);
lean_dec(v_dropped_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg(lean_object* v_param_35_){
_start:
{
lean_inc(v_param_35_);
return v_param_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___redArg___boxed(lean_object* v_param_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_FunIndParamKind_param_elim___redArg(v_param_36_);
lean_dec(v_param_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_param_41_){
_start:
{
lean_inc(v_param_41_);
return v_param_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_param_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_param_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_FunIndParamKind_param_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_param_45_);
lean_dec(v_param_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg(lean_object* v_target_48_){
_start:
{
lean_inc(v_target_48_);
return v_target_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___redArg___boxed(lean_object* v_target_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_FunIndParamKind_target_elim___redArg(v_target_49_);
lean_dec(v_target_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_target_54_){
_start:
{
lean_inc(v_target_54_);
return v_target_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_target_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_target_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_FunIndParamKind_target_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_target_58_);
lean_dec(v_target_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqFunIndParamKind_beq(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind_beq___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_x_24__boxed_70_; uint8_t v_y_25__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_24__boxed_70_ = lean_unbox(v_x_68_);
v_y_25__boxed_71_ = lean_unbox(v_y_69_);
v_res_72_ = l_Lean_Meta_instBEqFunIndParamKind_beq(v_x_24__boxed_70_, v_y_25__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr(uint8_t v_x_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___y_92_; lean_object* v___y_99_; lean_object* v___y_106_; 
switch(v_x_89_)
{
case 0:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_90_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_92_ = v___x_114_;
goto v___jp_91_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_92_ = v___x_115_;
goto v___jp_91_;
}
}
case 1:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1024u);
v___x_117_ = lean_nat_dec_le(v___x_116_, v_prec_90_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_99_ = v___x_118_;
goto v___jp_98_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_99_ = v___x_119_;
goto v___jp_98_;
}
}
default: 
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = lean_nat_dec_le(v___x_120_, v_prec_90_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__6, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6);
v___y_106_ = v___x_122_;
goto v___jp_105_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_instReprFunIndParamKind_repr___closed__7, &l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once, _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7);
v___y_106_ = v___x_123_;
goto v___jp_105_;
}
}
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__1));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_90_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__3));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_90_);
return v___x_104_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_107_ = ((lean_object*)(l_Lean_Meta_instReprFunIndParamKind_repr___closed__5));
lean_inc(v___y_106_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
v___x_111_ = l_Repr_addAppParen(v___x_110_, v_prec_90_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind_repr___boxed(lean_object* v_x_124_, lean_object* v_prec_125_){
_start:
{
uint8_t v_x_171__boxed_126_; lean_object* v_res_127_; 
v_x_171__boxed_126_ = lean_unbox(v_x_124_);
v_res_127_ = l_Lean_Meta_instReprFunIndParamKind_repr(v_x_171__boxed_126_, v_prec_125_);
lean_dec(v_prec_125_);
return v_res_127_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind_default(void){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind(void){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprFunIndInfo_repr_spec__2(lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_nat_to_int(v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_dec(v_x_141_);
return v_x_142_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_156_; 
v_head_144_ = lean_ctor_get(v_x_143_, 0);
v_tail_145_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_156_ == 0)
{
v___x_147_ = v_x_143_;
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_head_144_);
lean_dec(v_x_143_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
lean_inc(v_x_141_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 5);
lean_ctor_set(v___x_147_, 1, v_x_141_);
lean_ctor_set(v___x_147_, 0, v_x_142_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_x_142_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_x_141_);
v___x_150_ = v_reuseFailAlloc_155_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_unbox(v_head_144_);
lean_dec(v_head_144_);
v___x_152_ = l_Bool_repr___redArg(v___x_151_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_150_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v_x_142_ = v___x_153_;
v_x_143_ = v_tail_145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_dec(v_x_157_);
return v_x_158_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_172_; 
v_head_160_ = lean_ctor_get(v_x_159_, 0);
v_tail_161_ = lean_ctor_get(v_x_159_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_172_ == 0)
{
v___x_163_ = v_x_159_;
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_tail_161_);
lean_inc(v_head_160_);
lean_dec(v_x_159_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
lean_inc(v_x_157_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 5);
lean_ctor_set(v___x_163_, 1, v_x_157_);
lean_ctor_set(v___x_163_, 0, v_x_158_);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_x_158_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_x_157_);
v___x_166_ = v_reuseFailAlloc_171_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_unbox(v_head_160_);
lean_dec(v_head_160_);
v___x_168_ = l_Bool_repr___redArg(v___x_167_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_166_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_157_, v___x_169_, v_tail_161_);
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_175_; 
lean_dec(v_x_174_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_tail_176_; 
v_tail_176_ = lean_ctor_get(v_x_173_, 1);
if (lean_obj_tag(v_tail_176_) == 0)
{
lean_object* v_head_177_; uint8_t v___x_178_; lean_object* v___x_179_; 
lean_dec(v_x_174_);
v_head_177_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_177_);
lean_dec_ref_known(v_x_173_, 2);
v___x_178_ = lean_unbox(v_head_177_);
lean_dec(v_head_177_);
v___x_179_ = l_Bool_repr___redArg(v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_head_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc(v_tail_176_);
v_head_180_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_180_);
lean_dec_ref_known(v_x_173_, 2);
v___x_181_ = lean_unbox(v_head_180_);
lean_dec(v_head_180_);
v___x_182_ = l_Bool_repr___redArg(v___x_181_);
v___x_183_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(v_x_174_, v___x_182_, v_tail_176_);
return v___x_183_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0));
v___x_193_ = lean_string_length(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(lean_object* v_xs_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = lean_array_get_size(v_xs_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_207_ = lean_array_to_list(v_xs_203_);
v___x_208_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3));
v___x_209_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(v___x_207_, v___x_208_);
v___x_210_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6);
v___x_211_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7));
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_209_);
v___x_213_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8));
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_210_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = l_Std_Format_fill(v___x_215_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
lean_dec_ref(v_xs_203_);
v___x_217_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10));
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_dec(v_x_218_);
return v_x_219_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_234_; 
v_head_221_ = lean_ctor_get(v_x_220_, 0);
v_tail_222_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_234_ == 0)
{
v___x_224_ = v_x_220_;
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
lean_inc(v_x_218_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 5);
lean_ctor_set(v___x_224_, 1, v_x_218_);
lean_ctor_set(v___x_224_, 0, v_x_219_);
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_x_219_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_x_218_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_unbox(v_head_221_);
lean_dec(v_head_221_);
v___x_230_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_229_, v___x_228_);
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_227_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v_x_219_ = v___x_231_;
v_x_220_ = v_tail_222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_dec(v_x_235_);
return v_x_236_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_251_; 
v_head_238_ = lean_ctor_get(v_x_237_, 0);
v_tail_239_ = lean_ctor_get(v_x_237_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_251_ == 0)
{
v___x_241_ = v_x_237_;
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_head_238_);
lean_dec(v_x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_251_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
lean_inc(v_x_235_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 5);
lean_ctor_set(v___x_241_, 1, v_x_235_);
lean_ctor_set(v___x_241_, 0, v_x_236_);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_x_236_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_x_235_);
v___x_244_ = v_reuseFailAlloc_250_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_unbox(v_head_238_);
lean_dec(v_head_238_);
v___x_247_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_246_, v___x_245_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(v_x_235_, v___x_248_, v_tail_239_);
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(uint8_t v___y_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___y_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_255_){
_start:
{
uint8_t v___y_857__boxed_256_; lean_object* v_res_257_; 
v___y_857__boxed_256_ = lean_unbox(v___y_255_);
v_res_257_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___y_857__boxed_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v___x_260_; 
lean_dec(v_x_259_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v_tail_261_; 
v_tail_261_ = lean_ctor_get(v_x_258_, 1);
if (lean_obj_tag(v_tail_261_) == 0)
{
lean_object* v_head_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
lean_dec(v_x_259_);
v_head_262_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_head_262_);
lean_dec_ref_known(v_x_258_, 2);
v___x_263_ = lean_unbox(v_head_262_);
lean_dec(v_head_262_);
v___x_264_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_263_);
return v___x_264_;
}
else
{
lean_object* v_head_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_inc(v_tail_261_);
v_head_265_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_head_265_);
lean_dec_ref_known(v_x_258_, 2);
v___x_266_ = lean_unbox(v_head_265_);
lean_dec(v_head_265_);
v___x_267_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_266_);
v___x_268_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(v_x_259_, v___x_267_, v_tail_261_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(lean_object* v_xs_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_array_get_size(v_xs_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_273_ = lean_array_to_list(v_xs_269_);
v___x_274_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3));
v___x_275_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(v___x_273_, v___x_274_);
v___x_276_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6);
v___x_277_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7));
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_275_);
v___x_279_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8));
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_276_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = l_Std_Format_fill(v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
lean_dec_ref(v_xs_269_);
v___x_283_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10));
return v___x_283_;
}
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(11u);
v___x_298_ = lean_nat_to_int(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(14u);
v___x_303_ = lean_nat_to_int(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(13u);
v___x_308_ = lean_nat_to_int(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(10u);
v___x_313_ = lean_nat_to_int(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0));
v___x_316_ = lean_string_length(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___redArg(lean_object* v_x_323_){
_start:
{
lean_object* v_funName_324_; lean_object* v_funIndName_325_; lean_object* v_levelMask_326_; lean_object* v_params_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_funName_324_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_funName_324_);
v_funIndName_325_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_funIndName_325_);
v_levelMask_326_ = lean_ctor_get(v_x_323_, 2);
lean_inc_ref(v_levelMask_326_);
v_params_327_ = lean_ctor_get(v_x_323_, 3);
lean_inc_ref(v_params_327_);
lean_dec_ref(v_x_323_);
v___x_328_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5));
v___x_329_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6));
v___x_330_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_Lean_Name_reprPrec(v_funName_324_, v___x_331_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = 0;
v___x_335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_329_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2));
v___x_338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_box(1);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9));
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_328_);
v___x_344_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10);
v___x_345_ = l_Lean_Name_reprPrec(v_funIndName_325_, v___x_331_);
v___x_346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*1, v___x_334_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_337_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_339_);
v___x_351_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12));
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_328_);
v___x_354_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13);
v___x_355_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(v_levelMask_326_);
v___x_356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_334_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_353_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_337_);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_339_);
v___x_361_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15));
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_328_);
v___x_364_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16);
v___x_365_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(v_params_327_);
v___x_366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_334_);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_363_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19, &l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once, _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19);
v___x_370_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20));
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_368_);
v___x_372_ = ((lean_object*)(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21));
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_369_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_334_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr(lean_object* v_x_376_, lean_object* v_prec_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg(v_x_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo_repr___boxed(lean_object* v_x_379_, lean_object* v_prec_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_instReprFunIndInfo_repr(v_x_379_, v_prec_380_);
lean_dec(v_prec_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(lean_object* v_env_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___y_390_; uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_fst_396_; uint8_t v___x_397_; 
v___x_395_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v_fst_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_fst_396_);
lean_inc_ref(v_env_384_);
v___x_397_ = l_Lean_Environment_contains(v_env_384_, v_fst_396_, v___x_394_);
if (v___x_397_ == 0)
{
v___y_390_ = v_b_388_;
goto v___jp_389_;
}
else
{
lean_object* v___x_398_; 
lean_inc(v___x_395_);
v___x_398_ = lean_array_push(v_b_388_, v___x_395_);
v___y_390_ = v___x_398_;
goto v___jp_389_;
}
}
else
{
lean_dec_ref(v_env_384_);
return v_b_388_;
}
v___jp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_386_, v___x_391_);
v_i_386_ = v___x_392_;
v_b_388_ = v___y_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_399_, lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_, lean_object* v_b_403_){
_start:
{
size_t v_i_boxed_404_; size_t v_stop_boxed_405_; lean_object* v_res_406_; 
v_i_boxed_404_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(v_env_399_, v_as_400_, v_i_boxed_404_, v_stop_boxed_405_, v_b_403_);
lean_dec_ref(v_as_400_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(lean_object* v_env_407_, lean_object* v_as_408_, size_t v_i_409_, size_t v_stop_410_, lean_object* v_b_411_){
_start:
{
lean_object* v___y_413_; uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_eq(v_i_409_, v_stop_410_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v_fst_419_; uint8_t v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_418_ = lean_array_uget_borrowed(v_as_408_, v_i_409_);
v_fst_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = 1;
lean_inc_ref(v_env_407_);
v___x_421_ = l_Lean_Environment_setExporting(v_env_407_, v___x_420_);
lean_inc(v_fst_419_);
v___x_422_ = l_Lean_Environment_contains(v___x_421_, v_fst_419_, v___x_420_);
if (v___x_422_ == 0)
{
v___y_413_ = v_b_411_;
goto v___jp_412_;
}
else
{
lean_object* v___x_423_; 
lean_inc(v___x_418_);
v___x_423_ = lean_array_push(v_b_411_, v___x_418_);
v___y_413_ = v___x_423_;
goto v___jp_412_;
}
}
else
{
lean_dec_ref(v_env_407_);
return v_b_411_;
}
v___jp_412_:
{
size_t v___x_414_; size_t v___x_415_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_409_, v___x_414_);
v_i_409_ = v___x_415_;
v_b_411_ = v___y_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_424_, lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_stop_427_, lean_object* v_b_428_){
_start:
{
size_t v_i_boxed_429_; size_t v_stop_boxed_430_; lean_object* v_res_431_; 
v_i_boxed_429_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_stop_boxed_430_ = lean_unbox_usize(v_stop_427_);
lean_dec(v_stop_427_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_424_, v_as_425_, v_i_boxed_429_, v_stop_boxed_430_, v_b_428_);
lean_dec_ref(v_as_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_432_, lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_433_) == 0)
{
lean_object* v_k_434_; lean_object* v_v_435_; lean_object* v_l_436_; lean_object* v_r_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_k_434_ = lean_ctor_get(v_x_433_, 1);
v_v_435_ = lean_ctor_get(v_x_433_, 2);
v_l_436_ = lean_ctor_get(v_x_433_, 3);
v_r_437_ = lean_ctor_get(v_x_433_, 4);
v___x_438_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_432_, v_l_436_);
lean_inc(v_v_435_);
lean_inc(v_k_434_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_k_434_);
lean_ctor_set(v___x_439_, 1, v_v_435_);
v___x_440_ = lean_array_push(v___x_438_, v___x_439_);
v_init_432_ = v___x_440_;
v_x_433_ = v_r_437_;
goto _start;
}
else
{
return v_init_432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_442_, v_x_443_);
lean_dec(v_x_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(lean_object* v_env_449_, lean_object* v_s_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___y_453_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_463_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v___x_462_, v_s_450_);
v___x_464_ = lean_array_get_size(v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_466_ = lean_nat_dec_lt(v___x_451_, v___x_464_);
if (v___x_466_ == 0)
{
lean_dec_ref(v___x_463_);
v___y_453_ = v___x_465_;
goto v___jp_452_;
}
else
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((size_t)0ULL);
v___x_468_ = lean_usize_of_nat(v___x_464_);
lean_inc_ref(v_env_449_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(v_env_449_, v___x_463_, v___x_467_, v___x_468_, v___x_465_);
lean_dec_ref(v___x_463_);
v___y_453_ = v___x_469_;
goto v___jp_452_;
}
v___jp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_array_get_size(v___y_453_);
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_456_ = lean_nat_dec_lt(v___x_451_, v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec_ref(v_env_449_);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___y_453_);
return v___x_457_;
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_of_nat(v___x_454_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_449_, v___y_453_, v___x_458_, v___x_459_, v___x_455_);
lean_inc_ref(v___x_460_);
v___x_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_ctor_set(v___x_461_, 2, v___y_453_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_env_470_, lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(v_env_470_, v_s_471_);
lean_dec(v_s_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; 
v___f_484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_487_ = 0;
v___x_488_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_485_, v___x_486_, v___x_487_, v___f_484_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(lean_object* v_init_491_, lean_object* v_t_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_491_, v_t_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_494_, lean_object* v_t_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(v_init_494_, v_t_495_);
lean_dec(v_t_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* v_declName_503_, uint8_t v_unfolding_504_){
_start:
{
if (v_unfolding_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__1));
v___x_506_ = l_Lean_Name_append(v_declName_503_, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__3));
v___x_508_ = l_Lean_Name_append(v_declName_503_, v___x_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object* v_declName_509_, lean_object* v_unfolding_510_){
_start:
{
uint8_t v_unfolding_boxed_511_; lean_object* v_res_512_; 
v_unfolding_boxed_511_ = lean_unbox(v_unfolding_510_);
v_res_512_ = l_Lean_Meta_getFunInductName(v_declName_509_, v_unfolding_boxed_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* v_declName_519_, uint8_t v_unfolding_520_){
_start:
{
if (v_unfolding_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__1));
v___x_522_ = l_Lean_Name_append(v_declName_519_, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__3));
v___x_524_ = l_Lean_Name_append(v_declName_519_, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object* v_declName_525_, lean_object* v_unfolding_526_){
_start:
{
uint8_t v_unfolding_boxed_527_; lean_object* v_res_528_; 
v_unfolding_boxed_527_ = lean_unbox(v_unfolding_526_);
v_res_528_ = l_Lean_Meta_getFunCasesName(v_declName_525_, v_unfolding_boxed_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* v_declName_535_, uint8_t v_unfolding_536_){
_start:
{
if (v_unfolding_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__1));
v___x_538_ = l_Lean_Name_append(v_declName_535_, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__3));
v___x_540_ = l_Lean_Name_append(v_declName_535_, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object* v_declName_541_, lean_object* v_unfolding_542_){
_start:
{
uint8_t v_unfolding_boxed_543_; lean_object* v_res_544_; 
v_unfolding_boxed_543_ = lean_unbox(v_unfolding_542_);
v_res_544_ = l_Lean_Meta_getMutualInductName(v_declName_541_, v_unfolding_boxed_543_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
lean_ctor_set(v___x_550_, 4, v___x_548_);
lean_ctor_set(v___x_550_, 5, v___x_548_);
lean_ctor_set(v___x_550_, 6, v___x_548_);
lean_ctor_set(v___x_550_, 7, v___x_548_);
lean_ctor_set(v___x_550_, 8, v___x_548_);
lean_ctor_set(v___x_550_, 9, v___x_548_);
lean_ctor_set(v___x_550_, 10, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(32u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((size_t)5ULL);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_unsigned_to_nat(32u);
v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
lean_ctor_set(v___x_559_, 2, v___x_555_);
lean_ctor_set(v___x_559_, 3, v___x_555_);
lean_ctor_set_usize(v___x_559_, 4, v___x_554_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_box(1);
v___x_561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_560_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_597_, lean_object* v_declHint_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_env_603_; uint8_t v___x_604_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_st_ref_get(v___y_599_);
v_env_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_env_603_);
lean_dec(v___x_602_);
v___x_604_ = l_Lean_Name_isAnonymous(v_declHint_598_);
if (v___x_604_ == 0)
{
uint8_t v_isExporting_605_; 
v_isExporting_605_ = lean_ctor_get_uint8(v_env_603_, sizeof(void*)*13);
if (v_isExporting_605_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_env_603_);
lean_dec(v_declHint_598_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_msg_597_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
lean_inc_ref(v_env_603_);
v___x_607_ = l_Lean_Environment_setExporting(v_env_603_, v___x_604_);
lean_inc(v_declHint_598_);
lean_inc_ref(v___x_607_);
v___x_608_ = l_Lean_Environment_contains(v___x_607_, v_declHint_598_, v_isExporting_605_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v___x_607_);
lean_dec_ref(v_env_603_);
lean_dec(v_declHint_598_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_msg_597_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_c_615_; lean_object* v___x_616_; 
v___x_610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_612_ = l_Lean_Options_empty;
lean_inc_ref(v___x_607_);
v___x_613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_613_, 0, v___x_607_);
lean_ctor_set(v___x_613_, 1, v___x_610_);
lean_ctor_set(v___x_613_, 2, v___x_611_);
lean_ctor_set(v___x_613_, 3, v___x_612_);
lean_inc(v_declHint_598_);
v___x_614_ = l_Lean_MessageData_ofConstName(v_declHint_598_, v___x_604_);
v_c_615_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_615_, 0, v___x_613_);
lean_ctor_set(v_c_615_, 1, v___x_614_);
v___x_616_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_607_, v_declHint_598_);
lean_dec_ref(v___x_607_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref(v_env_603_);
lean_dec(v_declHint_598_);
v___x_617_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_c_615_);
v___x_619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Lean_MessageData_note(v___x_620_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v_msg_597_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_677_; 
v_val_624_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_677_ == 0)
{
v___x_626_ = v___x_616_;
v_isShared_627_ = v_isSharedCheck_677_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_616_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_677_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v_modules_629_; lean_object* v_moduleNames_630_; lean_object* v_mod_631_; uint8_t v___x_646_; 
v___x_628_ = l_Lean_Environment_header(v_env_603_);
lean_dec_ref(v_env_603_);
v_modules_629_ = lean_ctor_get(v___x_628_, 3);
lean_inc_ref(v_modules_629_);
v_moduleNames_630_ = lean_ctor_get(v___x_628_, 4);
lean_inc_ref(v_moduleNames_630_);
lean_dec_ref(v___x_628_);
v_mod_631_ = lean_array_get(v___x_601_, v_moduleNames_630_, v_val_624_);
lean_dec_ref(v_moduleNames_630_);
v___x_646_ = l_Lean_isPrivateName(v_declHint_598_);
lean_dec(v_declHint_598_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_modules_629_);
v___x_648_ = lean_nat_dec_lt(v_val_624_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_modules_629_);
lean_dec(v_val_624_);
goto v___jp_632_;
}
else
{
lean_object* v___x_649_; lean_object* v_toImport_650_; uint8_t v_isExported_651_; 
v___x_649_ = lean_array_fget(v_modules_629_, v_val_624_);
lean_dec(v_val_624_);
lean_dec_ref(v_modules_629_);
v_toImport_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_toImport_650_);
lean_dec(v___x_649_);
v_isExported_651_ = lean_ctor_get_uint8(v_toImport_650_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_650_);
if (v_isExported_651_ == 0)
{
goto v___jp_632_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_del_object(v___x_626_);
v___x_652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_c_615_);
v___x_654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_MessageData_ofName(v_mod_631_);
lean_inc_ref(v___x_656_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_656_);
v___x_661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_MessageData_note(v___x_662_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v_msg_597_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_modules_629_);
lean_del_object(v___x_626_);
lean_dec(v_val_624_);
v___x_666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v_c_615_);
v___x_668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_MessageData_ofName(v_mod_631_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_MessageData_note(v___x_673_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v_msg_597_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
v___jp_632_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_633_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_c_615_);
v___x_635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_MessageData_ofName(v_mod_631_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_MessageData_note(v___x_640_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v_msg_597_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 0);
lean_ctor_set(v___x_626_, 0, v___x_642_);
v___x_644_ = v___x_626_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_env_603_);
lean_dec(v_declHint_598_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_msg_597_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_679_, lean_object* v_declHint_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_679_, v_declHint_680_, v___y_681_);
lean_dec(v___y_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_684_, lean_object* v_declHint_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v___x_689_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_684_, v_declHint_685_, v___y_687_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_699_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = l_Lean_unknownIdentifierMessageTag;
v___x_695_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_700_, lean_object* v_declHint_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_700_, v_declHint_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_toCold_711_; lean_object* v_env_712_; lean_object* v_options_713_; uint8_t v___x_714_; lean_object* v_env_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_toCold_711_ = lean_ctor_get(v___y_707_, 0);
v_env_712_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_710_);
v_options_713_ = lean_ctor_get(v_toCold_711_, 2);
v___x_714_ = 0;
v_env_715_ = l_Lean_Environment_setRecordingDeps(v_env_712_, v___x_714_);
v___x_716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_717_ = lean_unsigned_to_nat(32u);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_717_);
lean_dec_ref(v___x_718_);
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_713_);
v___x_720_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_720_, 0, v_env_715_);
lean_ctor_set(v___x_720_, 1, v___x_716_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
lean_ctor_set(v___x_720_, 3, v_options_713_);
v___x_721_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_msgData_706_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_ref_732_; lean_object* v___x_733_; lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_ref_732_ = lean_ctor_get(v___y_729_, 2);
v___x_733_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_728_, v___y_729_, v___y_730_);
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc(v_ref_732_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_ref_732_);
lean_ctor_set(v___x_738_, 1, v_a_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 1);
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_748_, lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_toCold_753_; lean_object* v_currRecDepth_754_; lean_object* v_ref_755_; uint16_t v_optionFlags_756_; uint8_t v_suppressElabErrors_757_; uint8_t v_checkDeprecated_758_; uint8_t v_isRecordingDeps_759_; lean_object* v_ref_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_toCold_753_ = lean_ctor_get(v___y_750_, 0);
v_currRecDepth_754_ = lean_ctor_get(v___y_750_, 1);
v_ref_755_ = lean_ctor_get(v___y_750_, 2);
v_optionFlags_756_ = lean_ctor_get_uint16(v___y_750_, sizeof(void*)*3);
v_suppressElabErrors_757_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*3 + 2);
v_checkDeprecated_758_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*3 + 3);
v_isRecordingDeps_759_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*3 + 4);
v_ref_760_ = l_Lean_replaceRef(v_ref_748_, v_ref_755_);
lean_inc(v_currRecDepth_754_);
lean_inc_ref(v_toCold_753_);
v___x_761_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_761_, 0, v_toCold_753_);
lean_ctor_set(v___x_761_, 1, v_currRecDepth_754_);
lean_ctor_set(v___x_761_, 2, v_ref_760_);
lean_ctor_set_uint16(v___x_761_, sizeof(void*)*3, v_optionFlags_756_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 2, v_suppressElabErrors_757_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 3, v_checkDeprecated_758_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*3 + 4, v_isRecordingDeps_759_);
v___x_762_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_749_, v___x_761_, v___y_751_);
lean_dec_ref_known(v___x_761_, 3);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_763_, lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_763_, v_msg_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v_ref_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_769_, lean_object* v_msg_770_, lean_object* v_declHint_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; 
v___x_775_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_770_, v_declHint_771_, v___y_772_, v___y_773_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_769_, v_a_776_, v___y_772_, v___y_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_778_, lean_object* v_msg_779_, lean_object* v_declHint_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_778_, v_msg_779_, v_declHint_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v_ref_778_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_791_, lean_object* v_constName_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_796_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_797_ = 0;
lean_inc(v_constName_792_);
v___x_798_ = l_Lean_MessageData_ofConstName(v_constName_792_, v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_791_, v___x_801_, v_constName_792_, v___y_793_, v___y_794_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_803_, lean_object* v_constName_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_803_, v_constName_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_ref_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(lean_object* v_constName_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_ref_813_; lean_object* v___x_814_; 
v_ref_813_ = lean_ctor_get(v___y_810_, 2);
v___x_814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_813_, v_constName_809_, v___y_810_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(lean_object* v_constName_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v_env_825_; uint8_t v___x_826_; lean_object* v___x_827_; 
v___x_824_ = lean_st_ref_get(v___y_822_);
v_env_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref(v_env_825_);
lean_dec(v___x_824_);
v___x_826_ = 0;
lean_inc(v_constName_820_);
v___x_827_ = l_Lean_Environment_find_x3f(v_env_825_, v_constName_820_, v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_820_, v___y_821_, v___y_822_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_constName_820_);
v_val_829_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_827_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v___x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_val_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(lean_object* v_constName_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_constName_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t v_unfolding_842_, uint8_t v_cases_843_, lean_object* v_declName_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
lean_inc(v_declName_844_);
v___x_848_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_declName_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_888_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_888_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___y_854_; 
if (lean_obj_tag(v_a_849_) == 1)
{
lean_dec_ref_known(v_a_849_, 1);
lean_del_object(v___x_851_);
if (v_cases_843_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_getFunInductName(v_declName_844_, v_unfolding_842_);
v___y_854_ = v___x_882_;
goto v___jp_853_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_getFunCasesName(v_declName_844_, v_unfolding_842_);
v___y_854_ = v___x_883_;
goto v___jp_853_;
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v_a_849_);
lean_dec(v_declName_844_);
v___x_884_ = lean_box(0);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_884_);
v___x_886_ = v___x_851_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
v___jp_853_:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_realizeGlobalConstNoOverloadCore(v___y_854_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_864_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_881_; 
v_a_865_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_881_ == 0)
{
v___x_867_ = v___x_855_;
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_855_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_869_; 
v___x_869_ = l_Lean_Exception_isInterrupt(v_a_865_);
if (v___x_869_ == 0)
{
uint8_t v___x_870_; 
lean_inc(v_a_865_);
v___x_870_ = l_Lean_Exception_isRuntime(v_a_865_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_a_865_);
v___x_871_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 0);
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_876_; 
if (v_isShared_868_ == 0)
{
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_865_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v___x_879_; 
if (v_isShared_868_ == 0)
{
v___x_879_ = v___x_867_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_865_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_declName_844_);
v_a_889_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_848_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_848_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object* v_unfolding_897_, lean_object* v_cases_898_, lean_object* v_declName_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
uint8_t v_unfolding_boxed_903_; uint8_t v_cases_boxed_904_; lean_object* v_res_905_; 
v_unfolding_boxed_903_ = lean_unbox(v_unfolding_897_);
v_cases_boxed_904_ = lean_unbox(v_cases_898_);
v_res_905_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_boxed_903_, v_cases_boxed_904_, v_declName_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(lean_object* v_00_u03b1_906_, lean_object* v_constName_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_907_, v___y_908_, v___y_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_912_, lean_object* v_constName_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(v_00_u03b1_912_, v_constName_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_918_, lean_object* v_ref_919_, lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_919_, v_constName_920_, v___y_921_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_925_, lean_object* v_ref_926_, lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(v_00_u03b1_925_, v_ref_926_, v_constName_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_ref_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_932_, lean_object* v_ref_933_, lean_object* v_msg_934_, lean_object* v_declHint_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_933_, v_msg_934_, v_declHint_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_940_, lean_object* v_ref_941_, lean_object* v_msg_942_, lean_object* v_declHint_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_940_, v_ref_941_, v_msg_942_, v_declHint_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_ref_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_948_, v_declHint_949_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_954_, lean_object* v_declHint_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_954_, v_declHint_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_960_, lean_object* v_ref_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_961_, v_msg_962_, v___y_963_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_967_, lean_object* v_ref_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_967_, v_ref_968_, v_msg_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_ref_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_974_, lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_980_, lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_980_, v_msg_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(lean_object* v_msg_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___f_991_; lean_object* v___x_372__overap_992_; lean_object* v___x_993_; 
v___f_991_ = ((lean_object*)(l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0));
v___x_372__overap_992_ = lean_panic_fn_borrowed(v___f_991_, v_msg_987_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_993_ = lean_apply_3(v___x_372__overap_992_, v___y_988_, v___y_989_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v_msg_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__1(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__0, &l_Lean_Meta_setFunIndInfo___closed__0_once, _init_l_Lean_Meta_setFunIndInfo___closed__0);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__5(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__4));
v___x_1007_ = lean_unsigned_to_nat(2u);
v___x_1008_ = lean_unsigned_to_nat(79u);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__3));
v___x_1010_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__2));
v___x_1011_ = l_mkPanicMessageWithDecl(v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_, v___x_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object* v_funIndInfo_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v_env_1017_; lean_object* v_funIndName_1018_; lean_object* v___x_1019_; lean_object* v_toEnvExtension_1020_; lean_object* v_asyncMode_1021_; uint8_t v___x_1022_; 
v___x_1016_ = lean_st_ref_get(v_a_1014_);
v_env_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_ref(v_env_1017_);
lean_dec(v___x_1016_);
v_funIndName_1018_ = lean_ctor_get(v_funIndInfo_1012_, 1);
lean_inc_n(v_funIndName_1018_, 2);
v___x_1019_ = l_Lean_Meta_funIndInfoExt;
v_toEnvExtension_1020_ = lean_ctor_get(v___x_1019_, 0);
v_asyncMode_1021_ = lean_ctor_get(v_toEnvExtension_1020_, 2);
v___x_1022_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1019_, v_env_1017_, v_funIndName_1018_, v_asyncMode_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v_env_1024_; lean_object* v_nextMacroScope_1025_; lean_object* v_ngen_1026_; lean_object* v_auxDeclNGen_1027_; lean_object* v_traceState_1028_; lean_object* v_recordedDeps_1029_; lean_object* v_messages_1030_; lean_object* v_infoState_1031_; lean_object* v_snapshotTasks_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1044_; 
v___x_1023_ = lean_st_ref_take(v_a_1014_);
v_env_1024_ = lean_ctor_get(v___x_1023_, 0);
v_nextMacroScope_1025_ = lean_ctor_get(v___x_1023_, 1);
v_ngen_1026_ = lean_ctor_get(v___x_1023_, 2);
v_auxDeclNGen_1027_ = lean_ctor_get(v___x_1023_, 3);
v_traceState_1028_ = lean_ctor_get(v___x_1023_, 4);
v_recordedDeps_1029_ = lean_ctor_get(v___x_1023_, 6);
v_messages_1030_ = lean_ctor_get(v___x_1023_, 7);
v_infoState_1031_ = lean_ctor_get(v___x_1023_, 8);
v_snapshotTasks_1032_ = lean_ctor_get(v___x_1023_, 9);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1023_, 5);
lean_dec(v_unused_1045_);
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snapshotTasks_1032_);
lean_inc(v_infoState_1031_);
lean_inc(v_messages_1030_);
lean_inc(v_recordedDeps_1029_);
lean_inc(v_traceState_1028_);
lean_inc(v_auxDeclNGen_1027_);
lean_inc(v_ngen_1026_);
lean_inc(v_nextMacroScope_1025_);
lean_inc(v_env_1024_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1019_, v_env_1024_, v_funIndName_1018_, v_funIndInfo_1012_, v___x_1022_);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__1, &l_Lean_Meta_setFunIndInfo___closed__1_once, _init_l_Lean_Meta_setFunIndInfo___closed__1);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 5, v___x_1038_);
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_nextMacroScope_1025_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_ngen_1026_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_auxDeclNGen_1027_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_traceState_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1043_, 6, v_recordedDeps_1029_);
lean_ctor_set(v_reuseFailAlloc_1043_, 7, v_messages_1030_);
lean_ctor_set(v_reuseFailAlloc_1043_, 8, v_infoState_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 9, v_snapshotTasks_1032_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_st_ref_put(v_a_1014_, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1036_);
return v___x_1042_;
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v_funIndName_1018_);
lean_dec_ref(v_funIndInfo_1012_);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__5, &l_Lean_Meta_setFunIndInfo___closed__5_once, _init_l_Lean_Meta_setFunIndInfo___closed__5);
v___x_1047_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v___x_1046_, v_a_1013_, v_a_1014_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo___boxed(lean_object* v_funIndInfo_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_setFunIndInfo(v_funIndInfo_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object* v_inductName_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v_env_1057_; lean_object* v___x_1058_; lean_object* v_toEnvExtension_1059_; lean_object* v_asyncMode_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1056_ = lean_st_ref_get(v_a_1054_);
v_env_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc_ref(v_env_1057_);
lean_dec(v___x_1056_);
v___x_1058_ = l_Lean_Meta_funIndInfoExt;
v_toEnvExtension_1059_ = lean_ctor_get(v___x_1058_, 0);
v_asyncMode_1060_ = lean_ctor_get(v_toEnvExtension_1059_, 2);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1058_, v_env_1057_, v_inductName_1053_, v_asyncMode_1060_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object* v_inductName_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1064_, v_a_1065_);
lean_dec(v_a_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object* v_inductName_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1068_, v_a_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object* v_inductName_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_getFunIndInfoForInduct_x3f(v_inductName_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t v_cases_1078_, uint8_t v_unfolding_1079_, lean_object* v_funName_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_1079_, v_cases_1078_, v_funName_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1095_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_1087_);
v_val_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_a_1085_, 1);
v___x_1090_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_val_1089_, v_a_1082_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_dec(v_a_1085_);
v___x_1091_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1091_);
v___x_1093_ = v___x_1087_;
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
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1084_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1084_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object* v_cases_1104_, lean_object* v_unfolding_1105_, lean_object* v_funName_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v_cases_boxed_1110_; uint8_t v_unfolding_boxed_1111_; lean_object* v_res_1112_; 
v_cases_boxed_1110_ = lean_unbox(v_cases_1104_);
v_unfolding_boxed_1111_ = lean_unbox(v_unfolding_1105_);
v_res_1112_ = l_Lean_Meta_getFunIndInfo_x3f(v_cases_boxed_1110_, v_unfolding_boxed_1111_, v_funName_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1112_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedFunIndParamKind_default = _init_l_Lean_Meta_instInhabitedFunIndParamKind_default();
l_Lean_Meta_instInhabitedFunIndParamKind = _init_l_Lean_Meta_instInhabitedFunIndParamKind();
res = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_funIndInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
}
#ifdef __cplusplus
}
#endif
