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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_451_; lean_object* v___y_453_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_469_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v___x_468_, v_s_450_);
v___x_470_ = lean_array_get_size(v___x_469_);
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_472_ = lean_nat_dec_lt(v___x_451_, v___x_470_);
if (v___x_472_ == 0)
{
lean_dec_ref(v___x_469_);
v___y_453_ = v___x_471_;
goto v___jp_452_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_473_ == 0)
{
if (v___x_472_ == 0)
{
lean_dec_ref(v___x_469_);
v___y_453_ = v___x_471_;
goto v___jp_452_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_470_);
lean_inc_ref(v_env_449_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(v_env_449_, v___x_469_, v___x_474_, v___x_475_, v___x_471_);
lean_dec_ref(v___x_469_);
v___y_453_ = v___x_476_;
goto v___jp_452_;
}
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_470_);
lean_inc_ref(v_env_449_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__2(v_env_449_, v___x_469_, v___x_477_, v___x_478_, v___x_471_);
lean_dec_ref(v___x_469_);
v___y_453_ = v___x_479_;
goto v___jp_452_;
}
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
uint8_t v___x_458_; 
v___x_458_ = lean_nat_dec_le(v___x_454_, v___x_454_);
if (v___x_458_ == 0)
{
if (v___x_456_ == 0)
{
lean_object* v___x_459_; 
lean_dec_ref(v_env_449_);
v___x_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_455_);
lean_ctor_set(v___x_459_, 1, v___x_455_);
lean_ctor_set(v___x_459_, 2, v___y_453_);
return v___x_459_;
}
else
{
size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = ((size_t)0ULL);
v___x_461_ = lean_usize_of_nat(v___x_454_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_449_, v___y_453_, v___x_460_, v___x_461_, v___x_455_);
lean_inc_ref(v___x_462_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v___y_453_);
return v___x_463_;
}
}
else
{
size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = ((size_t)0ULL);
v___x_465_ = lean_usize_of_nat(v___x_454_);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_449_, v___y_453_, v___x_464_, v___x_465_, v___x_455_);
lean_inc_ref(v___x_466_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_ctor_set(v___x_467_, 2, v___y_453_);
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_env_480_, lean_object* v_s_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(v_env_480_, v_s_481_);
lean_dec(v_s_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
v___f_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_));
v___x_497_ = 0;
v___x_498_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_495_, v___x_496_, v___x_497_, v___f_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(lean_object* v_init_501_, lean_object* v_t_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_501_, v_t_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_504_, lean_object* v_t_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(v_init_504_, v_t_505_);
lean_dec(v_t_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* v_declName_513_, uint8_t v_unfolding_514_){
_start:
{
if (v_unfolding_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__1));
v___x_516_ = l_Lean_Name_append(v_declName_513_, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Meta_getFunInductName___closed__3));
v___x_518_ = l_Lean_Name_append(v_declName_513_, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object* v_declName_519_, lean_object* v_unfolding_520_){
_start:
{
uint8_t v_unfolding_boxed_521_; lean_object* v_res_522_; 
v_unfolding_boxed_521_ = lean_unbox(v_unfolding_520_);
v_res_522_ = l_Lean_Meta_getFunInductName(v_declName_519_, v_unfolding_boxed_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* v_declName_529_, uint8_t v_unfolding_530_){
_start:
{
if (v_unfolding_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__1));
v___x_532_ = l_Lean_Name_append(v_declName_529_, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Meta_getFunCasesName___closed__3));
v___x_534_ = l_Lean_Name_append(v_declName_529_, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object* v_declName_535_, lean_object* v_unfolding_536_){
_start:
{
uint8_t v_unfolding_boxed_537_; lean_object* v_res_538_; 
v_unfolding_boxed_537_ = lean_unbox(v_unfolding_536_);
v_res_538_ = l_Lean_Meta_getFunCasesName(v_declName_535_, v_unfolding_boxed_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* v_declName_545_, uint8_t v_unfolding_546_){
_start:
{
if (v_unfolding_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__1));
v___x_548_ = l_Lean_Name_append(v_declName_545_, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_getMutualInductName___closed__3));
v___x_550_ = l_Lean_Name_append(v_declName_545_, v___x_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object* v_declName_551_, lean_object* v_unfolding_552_){
_start:
{
uint8_t v_unfolding_boxed_553_; lean_object* v_res_554_; 
v_unfolding_boxed_553_ = lean_unbox(v_unfolding_552_);
v_res_554_ = l_Lean_Meta_getMutualInductName(v_declName_551_, v_unfolding_boxed_553_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_555_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
lean_ctor_set(v___x_561_, 3, v___x_560_);
lean_ctor_set(v___x_561_, 4, v___x_559_);
lean_ctor_set(v___x_561_, 5, v___x_559_);
lean_ctor_set(v___x_561_, 6, v___x_559_);
lean_ctor_set(v___x_561_, 7, v___x_559_);
lean_ctor_set(v___x_561_, 8, v___x_559_);
lean_ctor_set(v___x_561_, 9, v___x_559_);
lean_ctor_set(v___x_561_, 10, v___x_559_);
lean_ctor_set(v___x_561_, 11, v___x_558_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_unsigned_to_nat(32u);
v___x_563_ = lean_mk_empty_array_with_capacity(v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_565_ = ((size_t)5ULL);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_unsigned_to_nat(32u);
v___x_568_ = lean_mk_empty_array_with_capacity(v___x_567_);
v___x_569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_570_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_566_);
lean_ctor_set(v___x_570_, 3, v___x_566_);
lean_ctor_set_usize(v___x_570_, 4, v___x_565_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(1);
v___x_572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_608_, lean_object* v_declHint_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_env_614_; uint8_t v___x_615_; 
v___x_612_ = lean_box(0);
v___x_613_ = lean_st_ref_get(v___y_610_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
v___x_615_ = l_Lean_Name_isAnonymous(v_declHint_609_);
if (v___x_615_ == 0)
{
uint8_t v_isExporting_616_; 
v_isExporting_616_ = lean_ctor_get_uint8(v_env_614_, sizeof(void*)*13);
if (v_isExporting_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_env_614_);
lean_dec(v_declHint_609_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_msg_608_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
lean_inc_ref(v_env_614_);
v___x_618_ = l_Lean_Environment_setExporting(v_env_614_, v___x_615_);
lean_inc(v_declHint_609_);
lean_inc_ref(v___x_618_);
v___x_619_ = l_Lean_Environment_contains(v___x_618_, v_declHint_609_, v_isExporting_616_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec_ref(v___x_618_);
lean_dec_ref(v_env_614_);
lean_dec(v_declHint_609_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_msg_608_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_c_626_; lean_object* v___x_627_; 
v___x_621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_623_ = l_Lean_Options_empty;
v___x_624_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_624_, 0, v___x_618_);
lean_ctor_set(v___x_624_, 1, v___x_621_);
lean_ctor_set(v___x_624_, 2, v___x_622_);
lean_ctor_set(v___x_624_, 3, v___x_623_);
lean_inc(v_declHint_609_);
v___x_625_ = l_Lean_MessageData_ofConstName(v_declHint_609_, v___x_615_);
v_c_626_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_626_, 0, v___x_624_);
lean_ctor_set(v_c_626_, 1, v___x_625_);
v___x_627_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_614_, v_declHint_609_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_env_614_);
lean_dec(v_declHint_609_);
v___x_628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_c_626_);
v___x_630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_MessageData_note(v___x_631_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v_msg_608_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_691_; 
v_val_635_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_691_ == 0)
{
v___x_637_ = v___x_627_;
v_isShared_638_ = v_isSharedCheck_691_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_dec(v___x_627_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_691_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v_modules_640_; lean_object* v_moduleNames_641_; lean_object* v_mod_642_; uint8_t v___y_644_; uint8_t v___x_674_; 
v___x_639_ = l_Lean_Environment_header(v_env_614_);
lean_dec_ref(v_env_614_);
v_modules_640_ = lean_ctor_get(v___x_639_, 3);
lean_inc_ref(v_modules_640_);
v_moduleNames_641_ = lean_ctor_get(v___x_639_, 4);
lean_inc_ref(v_moduleNames_641_);
lean_dec_ref(v___x_639_);
v_mod_642_ = lean_array_get(v___x_612_, v_moduleNames_641_, v_val_635_);
lean_dec_ref(v_moduleNames_641_);
v___x_674_ = l_Lean_isPrivateName(v_declHint_609_);
lean_dec(v_declHint_609_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_modules_640_);
v___x_676_ = lean_nat_dec_lt(v_val_635_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec_ref(v_modules_640_);
lean_dec(v_val_635_);
v___y_644_ = v___x_674_;
goto v___jp_643_;
}
else
{
lean_object* v___x_677_; lean_object* v_toImport_678_; uint8_t v_isExported_679_; 
v___x_677_ = lean_array_fget(v_modules_640_, v_val_635_);
lean_dec(v_val_635_);
lean_dec_ref(v_modules_640_);
v_toImport_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_toImport_678_);
lean_dec(v___x_677_);
v_isExported_679_ = lean_ctor_get_uint8(v_toImport_678_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_678_);
v___y_644_ = v_isExported_679_;
goto v___jp_643_;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_modules_640_);
lean_del_object(v___x_637_);
lean_dec(v_val_635_);
v___x_680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v_c_626_);
v___x_682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_MessageData_ofName(v_mod_642_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_MessageData_note(v___x_687_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v_msg_608_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_c_626_);
v___x_647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_MessageData_ofName(v_mod_642_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_MessageData_note(v___x_652_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v_msg_608_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
lean_ctor_set(v___x_637_, 0, v___x_654_);
v___x_656_ = v___x_637_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_c_626_);
v___x_660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_MessageData_ofName(v_mod_642_);
lean_inc_ref(v___x_662_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_662_);
v___x_667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_MessageData_note(v___x_668_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v_msg_608_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
lean_ctor_set(v___x_637_, 0, v___x_670_);
v___x_672_ = v___x_637_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
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
lean_object* v___x_692_; 
lean_dec_ref(v_env_614_);
lean_dec(v_declHint_609_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_msg_608_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_693_, lean_object* v_declHint_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_693_, v_declHint_694_, v___y_695_);
lean_dec(v___y_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_698_, lean_object* v_declHint_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_713_; 
v___x_703_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_698_, v_declHint_699_, v___y_701_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_713_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = l_Lean_unknownIdentifierMessageTag;
v___x_709_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_a_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_709_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_714_, lean_object* v_declHint_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_714_, v_declHint_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_toCold_725_; lean_object* v_env_726_; lean_object* v_options_727_; uint8_t v___x_728_; lean_object* v_env_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_toCold_725_ = lean_ctor_get(v___y_721_, 0);
v_env_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_724_);
v_options_727_ = lean_ctor_get(v_toCold_725_, 2);
v___x_728_ = 0;
v_env_729_ = l_Lean_Environment_setRecordingDeps(v_env_726_, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_731_ = lean_unsigned_to_nat(32u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
lean_dec_ref(v___x_732_);
v___x_733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_727_);
v___x_734_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_734_, 0, v_env_729_);
lean_ctor_set(v___x_734_, 1, v___x_730_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
lean_ctor_set(v___x_734_, 3, v_options_727_);
v___x_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_msgData_720_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 2);
v___x_747_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_inc(v_ref_746_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_746_);
lean_ctor_set(v___x_752_, 1, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_toCold_767_; lean_object* v_currRecDepth_768_; lean_object* v_ref_769_; uint16_t v_optionFlags_770_; uint8_t v_suppressElabErrors_771_; uint8_t v_isRecordingDeps_772_; lean_object* v_ref_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_toCold_767_ = lean_ctor_get(v___y_764_, 0);
v_currRecDepth_768_ = lean_ctor_get(v___y_764_, 1);
v_ref_769_ = lean_ctor_get(v___y_764_, 2);
v_optionFlags_770_ = lean_ctor_get_uint16(v___y_764_, sizeof(void*)*3);
v_suppressElabErrors_771_ = lean_ctor_get_uint8(v___y_764_, sizeof(void*)*3 + 2);
v_isRecordingDeps_772_ = lean_ctor_get_uint8(v___y_764_, sizeof(void*)*3 + 3);
v_ref_773_ = l_Lean_replaceRef(v_ref_762_, v_ref_769_);
lean_inc(v_currRecDepth_768_);
lean_inc_ref(v_toCold_767_);
v___x_774_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_774_, 0, v_toCold_767_);
lean_ctor_set(v___x_774_, 1, v_currRecDepth_768_);
lean_ctor_set(v___x_774_, 2, v_ref_773_);
lean_ctor_set_uint16(v___x_774_, sizeof(void*)*3, v_optionFlags_770_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*3 + 2, v_suppressElabErrors_771_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*3 + 3, v_isRecordingDeps_772_);
v___x_775_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_763_, v___x_774_, v___y_765_);
lean_dec_ref_known(v___x_774_, 3);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_776_, v_msg_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v_ref_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_782_, lean_object* v_msg_783_, lean_object* v_declHint_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_790_; 
v___x_788_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_783_, v_declHint_784_, v___y_785_, v___y_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
v___x_790_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_782_, v_a_789_, v___y_785_, v___y_786_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_791_, lean_object* v_msg_792_, lean_object* v_declHint_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_791_, v_msg_792_, v_declHint_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_ref_791_);
return v_res_797_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_804_, lean_object* v_constName_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_809_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_810_ = 0;
lean_inc(v_constName_805_);
v___x_811_ = l_Lean_MessageData_ofConstName(v_constName_805_, v___x_810_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_809_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_804_, v___x_814_, v_constName_805_, v___y_806_, v___y_807_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_816_, lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_816_, v_constName_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v_ref_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_ref_826_; lean_object* v___x_827_; 
v_ref_826_ = lean_ctor_get(v___y_823_, 2);
v___x_827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_826_, v_constName_822_, v___y_823_, v___y_824_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(lean_object* v_constName_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_837_ = lean_st_ref_get(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = 0;
lean_inc(v_constName_833_);
v___x_840_ = l_Lean_Environment_find_x3f(v_env_838_, v_constName_833_, v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_833_, v___y_834_, v___y_835_);
return v___x_841_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_constName_833_);
v_val_842_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 0);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_val_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(lean_object* v_constName_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_constName_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t v_unfolding_855_, uint8_t v_cases_856_, lean_object* v_declName_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___y_862_; uint8_t v___y_863_; lean_object* v___x_867_; 
lean_inc(v_declName_857_);
v___x_867_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(v_declName_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_893_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_893_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_893_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_893_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___y_873_; 
if (lean_obj_tag(v_a_868_) == 1)
{
lean_dec_ref_known(v_a_868_, 1);
lean_del_object(v___x_870_);
if (v_cases_856_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_getFunInductName(v_declName_857_, v_unfolding_855_);
v___y_873_ = v___x_887_;
goto v___jp_872_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_getFunCasesName(v_declName_857_, v_unfolding_855_);
v___y_873_ = v___x_888_;
goto v___jp_872_;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_a_868_);
lean_dec(v_declName_857_);
v___x_889_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_889_);
v___x_891_ = v___x_870_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
v___jp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_realizeGlobalConstNoOverloadCore(v___y_873_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; uint8_t v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_874_, 1);
v___x_885_ = l_Lean_Exception_isInterrupt(v_a_884_);
if (v___x_885_ == 0)
{
uint8_t v___x_886_; 
lean_inc(v_a_884_);
v___x_886_ = l_Lean_Exception_isRuntime(v_a_884_);
v___y_862_ = v_a_884_;
v___y_863_ = v___x_886_;
goto v___jp_861_;
}
else
{
v___y_862_ = v_a_884_;
v___y_863_ = v___x_885_;
goto v___jp_861_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_declName_857_);
v_a_894_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_867_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_867_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
v___jp_861_:
{
if (v___y_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref(v___y_862_);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v___y_862_);
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object* v_unfolding_902_, lean_object* v_cases_903_, lean_object* v_declName_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_unfolding_boxed_908_; uint8_t v_cases_boxed_909_; lean_object* v_res_910_; 
v_unfolding_boxed_908_ = lean_unbox(v_unfolding_902_);
v_cases_boxed_909_ = lean_unbox(v_cases_903_);
v_res_910_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_boxed_908_, v_cases_boxed_909_, v_declName_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(lean_object* v_00_u03b1_911_, lean_object* v_constName_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_917_, lean_object* v_constName_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(v_00_u03b1_917_, v_constName_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_923_, lean_object* v_ref_924_, lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_924_, v_constName_925_, v___y_926_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_930_, lean_object* v_ref_931_, lean_object* v_constName_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(v_00_u03b1_930_, v_ref_931_, v_constName_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_ref_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_937_, lean_object* v_ref_938_, lean_object* v_msg_939_, lean_object* v_declHint_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_938_, v_msg_939_, v_declHint_940_, v___y_941_, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_945_, lean_object* v_ref_946_, lean_object* v_msg_947_, lean_object* v_declHint_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_945_, v_ref_946_, v_msg_947_, v_declHint_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v_ref_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_953_, lean_object* v_declHint_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_953_, v_declHint_954_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_959_, lean_object* v_declHint_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_959_, v_declHint_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_965_, lean_object* v_ref_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_966_, v_msg_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_972_, lean_object* v_ref_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_972_, v_ref_973_, v_msg_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v_ref_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_980_, v___y_981_, v___y_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_985_, v_msg_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_372__overap_997_; lean_object* v___x_998_; 
v___f_996_ = ((lean_object*)(l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0));
v___x_372__overap_997_ = lean_panic_fn_borrowed(v___f_996_, v_msg_992_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
v___x_998_ = lean_apply_3(v___x_372__overap_997_, v___y_993_, v___y_994_, lean_box(0));
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v_msg_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1003_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__0(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__1(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__0, &l_Lean_Meta_setFunIndInfo___closed__0_once, _init_l_Lean_Meta_setFunIndInfo___closed__0);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__5(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__4));
v___x_1012_ = lean_unsigned_to_nat(2u);
v___x_1013_ = lean_unsigned_to_nat(79u);
v___x_1014_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__3));
v___x_1015_ = ((lean_object*)(l_Lean_Meta_setFunIndInfo___closed__2));
v___x_1016_ = l_mkPanicMessageWithDecl(v___x_1015_, v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object* v_funIndInfo_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_env_1023_; lean_object* v_funIndName_1024_; lean_object* v___x_1025_; lean_object* v_toEnvExtension_1026_; lean_object* v_asyncMode_1027_; uint8_t v___x_1028_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_instInhabitedFunIndInfo_default));
v___x_1022_ = lean_st_ref_get(v_a_1019_);
v_env_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc_ref(v_env_1023_);
lean_dec(v___x_1022_);
v_funIndName_1024_ = lean_ctor_get(v_funIndInfo_1017_, 1);
lean_inc_n(v_funIndName_1024_, 2);
v___x_1025_ = l_Lean_Meta_funIndInfoExt;
v_toEnvExtension_1026_ = lean_ctor_get(v___x_1025_, 0);
v_asyncMode_1027_ = lean_ctor_get(v_toEnvExtension_1026_, 2);
v___x_1028_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1021_, v___x_1025_, v_env_1023_, v_funIndName_1024_, v_asyncMode_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v_env_1030_; lean_object* v_nextMacroScope_1031_; lean_object* v_ngen_1032_; lean_object* v_auxDeclNGen_1033_; lean_object* v_traceState_1034_; lean_object* v_recordedDeps_1035_; lean_object* v_messages_1036_; lean_object* v_infoState_1037_; lean_object* v_snapshotTasks_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1050_; 
v___x_1029_ = lean_st_ref_take(v_a_1019_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
v_nextMacroScope_1031_ = lean_ctor_get(v___x_1029_, 1);
v_ngen_1032_ = lean_ctor_get(v___x_1029_, 2);
v_auxDeclNGen_1033_ = lean_ctor_get(v___x_1029_, 3);
v_traceState_1034_ = lean_ctor_get(v___x_1029_, 4);
v_recordedDeps_1035_ = lean_ctor_get(v___x_1029_, 6);
v_messages_1036_ = lean_ctor_get(v___x_1029_, 7);
v_infoState_1037_ = lean_ctor_get(v___x_1029_, 8);
v_snapshotTasks_1038_ = lean_ctor_get(v___x_1029_, 9);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1029_, 5);
lean_dec(v_unused_1051_);
v___x_1040_ = v___x_1029_;
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snapshotTasks_1038_);
lean_inc(v_infoState_1037_);
lean_inc(v_messages_1036_);
lean_inc(v_recordedDeps_1035_);
lean_inc(v_traceState_1034_);
lean_inc(v_auxDeclNGen_1033_);
lean_inc(v_ngen_1032_);
lean_inc(v_nextMacroScope_1031_);
lean_inc(v_env_1030_);
lean_dec(v___x_1029_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1025_, v_env_1030_, v_funIndName_1024_, v_funIndInfo_1017_, v___x_1028_);
v___x_1044_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__1, &l_Lean_Meta_setFunIndInfo___closed__1_once, _init_l_Lean_Meta_setFunIndInfo___closed__1);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 5, v___x_1044_);
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_nextMacroScope_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_ngen_1032_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_auxDeclNGen_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_traceState_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 5, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1049_, 6, v_recordedDeps_1035_);
lean_ctor_set(v_reuseFailAlloc_1049_, 7, v_messages_1036_);
lean_ctor_set(v_reuseFailAlloc_1049_, 8, v_infoState_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 9, v_snapshotTasks_1038_);
v___x_1046_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_st_ref_put(v_a_1019_, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1042_);
return v___x_1048_;
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_funIndName_1024_);
lean_dec_ref(v_funIndInfo_1017_);
v___x_1052_ = lean_obj_once(&l_Lean_Meta_setFunIndInfo___closed__5, &l_Lean_Meta_setFunIndInfo___closed__5_once, _init_l_Lean_Meta_setFunIndInfo___closed__5);
v___x_1053_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v___x_1052_, v_a_1018_, v_a_1019_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo___boxed(lean_object* v_funIndInfo_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_setFunIndInfo(v_funIndInfo_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object* v_inductName_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_env_1064_; lean_object* v___x_1065_; lean_object* v_toEnvExtension_1066_; lean_object* v_asyncMode_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_instInhabitedFunIndInfo_default));
v___x_1063_ = lean_st_ref_get(v_a_1060_);
v_env_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_env_1064_);
lean_dec(v___x_1063_);
v___x_1065_ = l_Lean_Meta_funIndInfoExt;
v_toEnvExtension_1066_ = lean_ctor_get(v___x_1065_, 0);
v_asyncMode_1067_ = lean_ctor_get(v_toEnvExtension_1066_, 2);
v___x_1068_ = 0;
v___x_1069_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1062_, v___x_1065_, v_env_1064_, v_inductName_1059_, v_asyncMode_1067_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object* v_inductName_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1071_, v_a_1072_);
lean_dec(v_a_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object* v_inductName_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_1075_, v_a_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object* v_inductName_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_getFunIndInfoForInduct_x3f(v_inductName_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t v_cases_1085_, uint8_t v_unfolding_1086_, lean_object* v_funName_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_getFunInduct_x3f(v_unfolding_1086_, v_cases_1085_, v_funName_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
if (lean_obj_tag(v_a_1092_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1094_);
v_val_1096_ = lean_ctor_get(v_a_1092_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v_a_1092_, 1);
v___x_1097_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_val_1096_, v_a_1089_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_dec(v_a_1092_);
v___x_1098_ = lean_box(0);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1098_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1091_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1091_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object* v_cases_1111_, lean_object* v_unfolding_1112_, lean_object* v_funName_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_cases_boxed_1117_; uint8_t v_unfolding_boxed_1118_; lean_object* v_res_1119_; 
v_cases_boxed_1117_ = lean_unbox(v_cases_1111_);
v_unfolding_boxed_1118_ = lean_unbox(v_unfolding_1112_);
v_res_1119_ = l_Lean_Meta_getFunIndInfo_x3f(v_cases_boxed_1117_, v_unfolding_boxed_1118_, v_funName_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1119_;
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
