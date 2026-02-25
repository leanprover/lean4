// Lean compiler output
// Module: Lean.Message
// Imports: public import Init.Data.Slice.Array public import Lean.Util.PPExt public import Lean.Util.Sorry import Init.Data.String.Search import Init.Data.Format.Macro import Init.Data.Iterators.Consumers.Collect
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
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__0 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__0_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__1 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__1_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__2 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__2_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__3 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__3_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__4 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__4_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__5 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__5_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMessageSeverity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instBEqMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqMessageSeverity = (const lean_object*)&l_Lean_instBEqMessageSeverity___closed__0_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "information"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__0_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__0_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__1 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__1_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__2 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__3 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__3_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__4 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__5 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonMessageSeverity_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instToJsonMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonMessageSeverity = (const lean_object*)&l_Lean_instToJsonMessageSeverity___closed__0_value;
static const lean_string_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value)}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__1_value;
static const lean_string_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__2 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value)}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__3 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_instFromJsonMessageSeverity_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__4;
static lean_once_cell_t l_Lean_instFromJsonMessageSeverity_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonMessageSeverity_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__6;
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonMessageSeverity_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonMessageSeverity = (const lean_object*)&l_Lean_instFromJsonMessageSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageSeverity_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instToStringMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringMessageSeverity = (const lean_object*)&l_Lean_instToStringMessageSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMVarId_default;
static lean_once_cell_t l_Lean_instInhabitedMessageData_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageData_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MessageData_nil___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_nil___closed__0;
LEAN_EXPORT lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_ofSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofSyntax___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_ofSyntax___closed__0 = (const lean_object*)&l_Lean_MessageData_ofSyntax___closed__0_value;
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_ofConstName___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__0 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__0_value;
static const lean_string_object l_Lean_MessageData_ofConstName___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fullNames"};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__1 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_ofConstName___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_MessageData_ofConstName___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 29, 178, 193, 83, 135, 18, 31)}};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__2 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__2_value;
lean_object* l_Lean_ppConstNameWithInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0;
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1;
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "maxTraceChildren"};
static const lean_object* l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 113, 99, 32, 64, 25, 169, 239)}};
static const lean_object* l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Maximum number of trace node children to display"};
static const lean_object* l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(175, 61, 140, 215, 80, 247, 40, 222)}};
static const lean_object* l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_maxTraceChildren;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object*);
lean_object* l_instMonadST(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_mkErrorStringWithPos___closed__1_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__0 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_formatAux___closed__1;
static const lean_string_object l_Lean_MessageData_formatAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_MessageData_formatAux___closed__2 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__2_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__2_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__3 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__3_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_MessageData_formatAux___closed__4 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__4_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__4_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__5 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__5_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_MessageData_formatAux___closed__6 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__6_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__6_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__7 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__7_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_MessageData_formatAux___closed__8 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__8_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__8_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__9 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__9_value;
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_MessageData_formatAux___closed__10;
static const lean_string_object l_Lean_MessageData_formatAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.Message"};
static const lean_object* l_Lean_MessageData_formatAux___closed__11 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__11_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.MessageData.formatAux"};
static const lean_object* l_Lean_MessageData_formatAux___closed__12 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__12_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "MessageData.ofLazy: expected MessageData in Dynamic, got "};
static const lean_object* l_Lean_MessageData_formatAux___closed__13 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__13_value;
lean_object* l_Lean_formatRawGoal(lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
uint8_t lean_float_beq(double, double);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MessageData_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MessageData_format___closed__0 = (const lean_object*)&l_Lean_MessageData_format___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instAppend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instAppend___closed__0 = (const lean_object*)&l_Lean_MessageData_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instAppend = (const lean_object*)&l_Lean_MessageData_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofFormat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value),((lean_object*)&l_Lean_MessageData_instCoeString___closed__0_value)} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__2 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeString = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeFormat = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
static const lean_closure_object l_Lean_MessageData_instCoeLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofLevel, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeLevel___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeLevel = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeExpr = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeName___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeName = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofSyntax, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeSyntax___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeSyntax = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeMVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeMVarId___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeMVarId = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
static const lean_string_object l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeOptionExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeOptionExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeOptionExpr = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__0;
static const lean_string_object l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__1 = (const lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_arrayExpr_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value)}};
static const lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__2 = (const lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeArrayExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeArrayExpr = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___closed__0_value;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_ofList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_Lean_MessageData_ofList___closed__0 = (const lean_object*)&l_Lean_MessageData_ofList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_ofList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_ofList___closed__1 = (const lean_object*)&l_Lean_MessageData_ofList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__2;
static const lean_string_object l_Lean_MessageData_ofList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_MessageData_ofList___closed__3 = (const lean_object*)&l_Lean_MessageData_ofList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_ofList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_ofList___closed__4 = (const lean_object*)&l_Lean_MessageData_ofList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__5;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__6;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__7;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object*);
static const lean_string_object l_Lean_MessageData_orList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "– none –"};
static const lean_object* l_Lean_MessageData_orList___closed__0 = (const lean_object*)&l_Lean_MessageData_orList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__1 = (const lean_object*)&l_Lean_MessageData_orList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__2;
static const lean_string_object l_Lean_MessageData_orList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l_Lean_MessageData_orList___closed__3 = (const lean_object*)&l_Lean_MessageData_orList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__4 = (const lean_object*)&l_Lean_MessageData_orList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__5;
static const lean_string_object l_Lean_MessageData_orList___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", or "};
static const lean_object* l_Lean_MessageData_orList___closed__6 = (const lean_object*)&l_Lean_MessageData_orList___closed__6_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__6_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__7 = (const lean_object*)&l_Lean_MessageData_orList___closed__7_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__8;
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object*);
static const lean_string_object l_Lean_MessageData_andList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lean_MessageData_andList___closed__0 = (const lean_object*)&l_Lean_MessageData_andList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_andList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_andList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_andList___closed__1 = (const lean_object*)&l_Lean_MessageData_andList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_andList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_andList___closed__2;
static const lean_string_object l_Lean_MessageData_andList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", and "};
static const lean_object* l_Lean_MessageData_andList___closed__3 = (const lean_object*)&l_Lean_MessageData_andList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_andList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_andList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_andList___closed__4 = (const lean_object*)&l_Lean_MessageData_andList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_andList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_andList___closed__5;
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object*);
static lean_once_cell_t l_Lean_MessageData_note___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__0;
static const lean_string_object l_Lean_MessageData_note___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Note: "};
static const lean_object* l_Lean_MessageData_note___closed__1 = (const lean_object*)&l_Lean_MessageData_note___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_note___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_note___closed__1_value)}};
static const lean_object* l_Lean_MessageData_note___closed__2 = (const lean_object*)&l_Lean_MessageData_note___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_note___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__3;
static lean_once_cell_t l_Lean_MessageData_note___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__4;
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object*);
static const lean_string_object l_Lean_MessageData_hint_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Hint: "};
static const lean_object* l_Lean_MessageData_hint_x27___closed__0 = (const lean_object*)&l_Lean_MessageData_hint_x27___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_hint_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_hint_x27___closed__0_value)}};
static const lean_object* l_Lean_MessageData_hint_x27___closed__1 = (const lean_object*)&l_Lean_MessageData_hint_x27___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_hint_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_hint_x27___closed__2;
static lean_once_cell_t l_Lean_MessageData_hint_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_hint_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofList, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeList___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeList___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeList = (const lean_object*)&l_Lean_MessageData_instCoeList___closed__0_value;
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeListExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeListExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeListExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeListExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeListExpr = (const lean_object*)&l_Lean_MessageData_instCoeListExpr___closed__0_value;
extern lean_object* l_Lean_instInhabitedPosition_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonPosition_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPosition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "endPos"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "keepFullRange"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isSilent"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caption"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value;
lean_object* l_id___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10;
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0_value;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "BaseMessage"};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 105, 232, 242, 0, 63, 252, 70)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 201, 140, 230, 1, 55, 95, 217)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10;
lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonPosition_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value;
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value)} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 71, 4, 163, 123, 133, 137, 84)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20;
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 109, 20, 206, 1, 23, 246, 165)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(220, 87, 21, 107, 78, 188, 130, 35)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(6, 63, 220, 237, 219, 125, 166, 5)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(42, 121, 35, 234, 39, 185, 10, 205)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(157, 185, 242, 82, 251, 25, 14, 198)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41;
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToJsonSerialMessage_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_instToJsonSerialMessage_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonSerialMessage_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonSerialMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonSerialMessage_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonSerialMessage___closed__0 = (const lean_object*)&l_Lean_instToJsonSerialMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonSerialMessage = (const lean_object*)&l_Lean_instToJsonSerialMessage___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SerialMessage"};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 10, 29, 109, 171, 11, 228, 164)}};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__2;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__3;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__4;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__6;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__7;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__8;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__9;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__10;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__11;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__12;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__13;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__14;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__15;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__16;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__17;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__18;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__19;
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonSerialMessage_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 186, 66, 236, 16, 221, 215, 158)}};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__20 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__21;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__22;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonSerialMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonSerialMessage_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonSerialMessage___closed__0 = (const lean_object*)&l_Lean_instFromJsonSerialMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonSerialMessage = (const lean_object*)&l_Lean_instFromJsonSerialMessage___closed__0_value;
static const lean_string_object l_Lean_errorNameSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_errorNameSuffix___closed__0 = (const lean_object*)&l_Lean_errorNameSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_errorNameSuffix = (const lean_object*)&l_Lean_errorNameSuffix___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nested"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0 = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object*);
static const lean_ctor_object l_Lean_SerialMessage_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value)}};
static const lean_object* l_Lean_SerialMessage_toString___closed__0 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__0_value;
static const lean_ctor_object l_Lean_SerialMessage_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value)}};
static const lean_object* l_Lean_SerialMessage_toString___closed__1 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__1_value;
static const lean_string_object l_Lean_SerialMessage_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l_Lean_SerialMessage_toString___closed__2 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__2_value;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_SerialMessage_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SerialMessage_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SerialMessage_instToString___closed__0 = (const lean_object*)&l_Lean_SerialMessage_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SerialMessage_instToString = (const lean_object*)&l_Lean_SerialMessage_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedMessageLog_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageLog_default___closed__0;
extern lean_object* l_Lean_NameSet_empty;
static lean_once_cell_t l_Lean_instInhabitedMessageLog_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageLog_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__0;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__1;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__2;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageLog_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageLog_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageLog_instAppend___closed__0 = (const lean_object*)&l_Lean_MessageLog_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageLog_instAppend = (const lean_object*)&l_Lean_MessageLog_instAppend___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0;
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__2;
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__3 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__3_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__4 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__5;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_inlineExprTrailing___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_inlineExprTrailing___lam__0___closed__0 = (const lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_inlineExprTrailing___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__0_value)}};
static const lean_object* l_Lean_inlineExprTrailing___lam__0___closed__1 = (const lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_inlineExprTrailing___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExprTrailing___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object*, lean_object*);
static const lean_string_object l_Lean_aquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "「"};
static const lean_object* l_Lean_aquote___closed__0 = (const lean_object*)&l_Lean_aquote___closed__0_value;
static const lean_ctor_object l_Lean_aquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_aquote___closed__0_value)}};
static const lean_object* l_Lean_aquote___closed__1 = (const lean_object*)&l_Lean_aquote___closed__1_value;
static lean_once_cell_t l_Lean_aquote___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_aquote___closed__2;
static const lean_string_object l_Lean_aquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "」"};
static const lean_object* l_Lean_aquote___closed__3 = (const lean_object*)&l_Lean_aquote___closed__3_value;
static const lean_ctor_object l_Lean_aquote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_aquote___closed__3_value)}};
static const lean_object* l_Lean_aquote___closed__4 = (const lean_object*)&l_Lean_aquote___closed__4_value;
static lean_once_cell_t l_Lean_aquote___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_aquote___closed__5;
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_stringToMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_stringToMessageData___closed__0;
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataExpr = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataLevel = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataName = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
static const lean_closure_object l_Lean_instToMessageDataString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_stringToMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataString___closed__0 = (const lean_object*)&l_Lean_instToMessageDataString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataString = (const lean_object*)&l_Lean_instToMessageDataString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataSyntax = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataFormat = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataMVarId = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
static const lean_closure_object l_Lean_instToMessageDataMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToMessageDataMessageData___closed__0 = (const lean_object*)&l_Lean_instToMessageDataMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataMessageData = (const lean_object*)&l_Lean_instToMessageDataMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0;
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToMessageDataSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMessageDataSubarray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataSubarray___redArg___closed__0 = (const lean_object*)&l_Lean_instToMessageDataSubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "some ("};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_mkErrorStringWithPos___closed__4_value)}};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToMessageDataOptionExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToMessageDataOptionExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMessageDataOptionExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataOptionExpr___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataOptionExpr = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___closed__0_value;
static const lean_string_object l_Lean_termM_x21___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean_termM_x21___00__closed__0 = (const lean_object*)&l_Lean_termM_x21___00__closed__0_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__1_value_aux_0),((lean_object*)&l_Lean_termM_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean_termM_x21___00__closed__1 = (const lean_object*)&l_Lean_termM_x21___00__closed__1_value;
static const lean_string_object l_Lean_termM_x21___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termM_x21___00__closed__2 = (const lean_object*)&l_Lean_termM_x21___00__closed__2_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termM_x21___00__closed__3 = (const lean_object*)&l_Lean_termM_x21___00__closed__3_value;
static const lean_string_object l_Lean_termM_x21___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean_termM_x21___00__closed__4 = (const lean_object*)&l_Lean_termM_x21___00__closed__4_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__4_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__5 = (const lean_object*)&l_Lean_termM_x21___00__closed__5_value;
static const lean_string_object l_Lean_termM_x21___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_termM_x21___00__closed__6 = (const lean_object*)&l_Lean_termM_x21___00__closed__6_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_termM_x21___00__closed__7 = (const lean_object*)&l_Lean_termM_x21___00__closed__7_value;
static const lean_string_object l_Lean_termM_x21___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_termM_x21___00__closed__8 = (const lean_object*)&l_Lean_termM_x21___00__closed__8_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_termM_x21___00__closed__9 = (const lean_object*)&l_Lean_termM_x21___00__closed__9_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termM_x21___00__closed__10 = (const lean_object*)&l_Lean_termM_x21___00__closed__10_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__7_value),((lean_object*)&l_Lean_termM_x21___00__closed__10_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__11 = (const lean_object*)&l_Lean_termM_x21___00__closed__11_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__3_value),((lean_object*)&l_Lean_termM_x21___00__closed__5_value),((lean_object*)&l_Lean_termM_x21___00__closed__11_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__12 = (const lean_object*)&l_Lean_termM_x21___00__closed__12_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__12_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__13 = (const lean_object*)&l_Lean_termM_x21___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_termM_x21__ = (const lean_object*)&l_Lean_termM_x21___00__closed__13_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5_value;
static const lean_string_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toMessageData"};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value;
static lean_once_cell_t l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 4, 57, 33, 167, 136, 170, 64)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8_value;
static const lean_string_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ToMessageData"};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(14, 83, 41, 225, 154, 14, 42, 20)}};
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 56, 87, 160, 191, 253, 244, 156)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_toMessageList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_toMessageList___closed__0 = (const lean_object*)&l_Lean_toMessageList___closed__0_value;
static lean_once_cell_t l_Lean_toMessageList___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toMessageList___closed__1;
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object*);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "(kernel) declaration type mismatch, '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "' has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nbut it is expected to have type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__0;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__1;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__2;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) unknown constant '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__3 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__3_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__4;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__5 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__5_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__6;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "(kernel) constant has already been declared '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__7 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__7_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__8;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) declaration type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__9 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__10 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__10_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__11;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) declaration has metavariables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__12 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__12_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__13;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "(kernel) declaration has free variables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__14 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__14_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__15;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', expression: "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__16 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__16_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__17;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) function expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__18 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__18_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__19;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "(kernel) type expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__20 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__20_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__21;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) let-declaration type mismatch '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__22 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__22_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__23;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "(kernel) type mismatch at"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__24 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__24_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__25;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) application type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__26 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__26_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__27;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nargument has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__28 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__28_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__29;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nbut function has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__30 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__30_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__31;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) invalid projection"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__32 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__32_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__33;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) type of theorem '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__34 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__34_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__35;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "' is not a proposition"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__36 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__36_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__37;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "(kernel) "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__38 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__38_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__39;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "(kernel) deterministic timeout"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__40 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__41 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__41_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__42;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "(kernel) excessive memory consumption detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__43 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__44 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__44_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__45;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "(kernel) deep recursion detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__46 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__47 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__47_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__48;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "(kernel) interrupted"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__49 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__50 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__50_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__51;
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_40; lean_object* x_41; lean_object* x_46; lean_object* x_65; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_68; 
x_68 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_65 = x_68;
goto block_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_4, 0);
lean_inc(x_69);
lean_dec_ref(x_4);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__5));
x_73 = l_Nat_reprFast(x_70);
x_74 = lean_string_append(x_72, x_73);
lean_dec_ref(x_73);
x_75 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
x_76 = lean_string_append(x_74, x_75);
x_77 = l_Nat_reprFast(x_71);
x_78 = lean_string_append(x_76, x_77);
lean_dec_ref(x_77);
x_65 = x_78;
goto block_67;
}
block_24:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
x_12 = lean_string_append(x_1, x_11);
x_13 = l_Nat_reprFast(x_9);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_11);
x_16 = l_Nat_reprFast(x_10);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = lean_string_append(x_17, x_7);
lean_dec_ref(x_7);
x_19 = lean_string_append(x_18, x_11);
x_20 = lean_string_append(x_19, x_8);
lean_dec_ref(x_8);
x_21 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_3);
return x_23;
}
block_31:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
x_30 = lean_string_append(x_28, x_29);
x_7 = x_26;
x_8 = x_30;
goto block_24;
}
block_39:
{
lean_object* x_36; 
x_36 = lean_string_append(x_33, x_35);
lean_dec_ref(x_35);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_37; 
x_37 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_25 = x_36;
x_26 = x_34;
x_27 = x_37;
goto block_31;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec_ref(x_32);
x_25 = x_36;
x_26 = x_34;
x_27 = x_38;
goto block_31;
}
}
block_45:
{
lean_object* x_42; 
x_42 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__1));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_43; 
x_43 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_32 = x_41;
x_33 = x_42;
x_34 = x_40;
x_35 = x_43;
goto block_39;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec_ref(x_5);
x_32 = x_41;
x_33 = x_42;
x_34 = x_40;
x_35 = x_44;
goto block_39;
}
}
block_64:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_40 = x_46;
x_41 = x_47;
goto block_45;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_6);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
x_51 = 1;
x_52 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_49, x_51);
x_53 = lean_string_append(x_50, x_52);
lean_dec_ref(x_52);
x_54 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
x_55 = lean_string_append(x_53, x_54);
lean_ctor_set(x_6, 0, x_55);
x_40 = x_46;
x_41 = x_6;
goto block_45;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_6, 0);
lean_inc(x_56);
lean_dec(x_6);
x_57 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
x_58 = 1;
x_59 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_56, x_58);
x_60 = lean_string_append(x_57, x_59);
lean_dec_ref(x_59);
x_61 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_40 = x_46;
x_41 = x_63;
goto block_45;
}
}
}
block_67:
{
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_66; 
x_66 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_7 = x_65;
x_8 = x_66;
goto block_24;
}
else
{
x_46 = x_65;
goto block_64;
}
}
else
{
x_46 = x_65;
goto block_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkErrorStringWithPos(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_MessageSeverity_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_MessageSeverity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_MessageSeverity_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_information_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_MessageSeverity_information_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_warning_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_MessageSeverity_warning_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageSeverity_error_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_MessageSeverity_error_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_MessageSeverity_ctorIdx(x_1);
x_4 = l_Lean_MessageSeverity_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_instBEqMessageSeverity_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToJsonMessageSeverity_toJson(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__5(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getTag_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_obj_once(&l_Lean_instFromJsonMessageSeverity_fromJson___closed__4, &l_Lean_instFromJsonMessageSeverity_fromJson___closed__4_once, _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__4);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_obj_once(&l_Lean_instFromJsonMessageSeverity_fromJson___closed__5, &l_Lean_instFromJsonMessageSeverity_fromJson___closed__5_once, _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_obj_once(&l_Lean_instFromJsonMessageSeverity_fromJson___closed__6, &l_Lean_instFromJsonMessageSeverity_fromJson___closed__6_once, _init_l_Lean_instFromJsonMessageSeverity_fromJson___closed__6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_MessageSeverity_toString(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
case 6:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
case 8:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
case 9:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_3(x_2, x_15, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_apply_2(x_2, x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MessageData_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MessageData_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedMVarId_default;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instInhabitedMessageData_default___closed__0, &l_Lean_instInhabitedMessageData_default___closed__0_once, _init_l_Lean_instInhabitedMessageData_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageData_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_2, x_10, lean_box(0));
x_6 = x_11;
x_7 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = lean_apply_2(x_3, x_12, lean_box(0));
x_6 = x_13;
x_7 = lean_box(0);
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MessageData_lazy___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_5 = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_1);
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_2 = x_3;
goto _start;
}
case 4:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_2 = x_5;
goto _start;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_2 = x_7;
goto _start;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_2 = x_9;
goto _start;
}
case 7:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Lean_MessageData_hasTag(x_1, x_11);
if (x_13 == 0)
{
x_2 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_1);
return x_13;
}
}
case 8:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
x_2 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_16);
lean_dec_ref(x_1);
x_20 = lean_unbox(x_17);
return x_20;
}
}
case 9:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_25 = lean_apply_1(x_1, x_24);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc_ref(x_1);
x_27 = l_Lean_MessageData_hasTag(x_1, x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_23);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_1);
return x_27;
}
else
{
if (x_30 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_1);
return x_27;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_29);
x_33 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(x_1, x_23, x_31, x_32);
lean_dec_ref(x_23);
return x_33;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_1);
return x_27;
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_1);
x_34 = lean_unbox(x_25);
return x_34;
}
}
default: 
{
uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = 0;
return x_35;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l_Lean_MessageData_hasTag(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_7;
}
}
else
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_hasTag(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
case 4:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_kind(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
case 4:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 9:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isTrace(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_MessageData_composePreservingKind(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Lean_MessageData_composePreservingKind(x_7, x_2);
x_9 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 4:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_MessageData_composePreservingKind(x_11, x_2);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_MessageData_composePreservingKind(x_14, x_2);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 8:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_19);
x_20 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_mkPPContext(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofSyntax___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = 0;
x_12 = l_Lean_Syntax_formatStx(x_2, x_10, x_11);
x_5 = x_12;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = l_Lean_ppTerm(x_13, x_2);
x_5 = x_14;
x_6 = lean_box(0);
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MessageData_ofFormat(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ofSyntax___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
x_3 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_4 = lean_box(0);
x_5 = l_Lean_Syntax_copyHeadTailInfoFrom(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_instantiateMVarsCore(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Expr_hasSyntheticSorry(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofExpr___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_expr_dbg_to_string(x_2);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_5 = x_13;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = l_Lean_ppExprWithInfos(x_14, x_2);
x_5 = x_15;
x_6 = lean_box(0);
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ofExpr___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Level_format(x_2, x_10);
x_5 = x_11;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l_Lean_ppLevel(x_12, x_2);
x_5 = x_13;
x_6 = lean_box(0);
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MessageData_ofFormat(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_ofLevel___lam__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
x_3 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__1___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_MessageData_ofFormat(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_7, x_5);
if (x_6 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_10);
return x_1;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_3);
lean_inc(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_13, x_11);
if (x_12 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
x_16 = l_Lean_Name_isPrefixOf(x_15, x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 1;
x_14 = l_Lean_Name_toString(x_2, x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_6 = x_17;
x_7 = lean_box(0);
goto block_10;
}
else
{
if (x_3 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec_ref(x_4);
x_19 = l_Lean_ppConstNameWithInfos(x_18, x_2);
x_11 = x_19;
goto block_12;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec_ref(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 3);
x_23 = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
x_24 = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(x_22, x_23, x_3);
lean_ctor_set(x_20, 3, x_24);
x_25 = l_Lean_ppConstNameWithInfos(x_20, x_2);
x_11 = x_25;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 2);
x_29 = lean_ctor_get(x_20, 3);
x_30 = lean_ctor_get(x_20, 4);
x_31 = lean_ctor_get(x_20, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_32 = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
x_33 = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(x_29, x_32, x_3);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
x_35 = l_Lean_ppConstNameWithInfos(x_34, x_2);
x_11 = x_35;
goto block_12;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
block_12:
{
x_6 = x_11;
x_7 = lean_box(0);
goto block_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_MessageData_ofConstName___lam__1(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
x_4 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_5 = lean_box(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_MessageData_ofConstName(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_7, x_8);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_1 = x_14;
x_2 = x_12;
goto _start;
}
case 4:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_2 = x_16;
goto _start;
}
case 5:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
x_2 = x_18;
goto _start;
}
case 6:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_2 = x_20;
goto _start;
}
case 7:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_23);
lean_dec_ref(x_2);
lean_inc(x_1);
x_24 = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(x_1, x_22);
if (x_24 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
lean_dec_ref(x_23);
lean_dec(x_1);
return x_24;
}
}
case 8:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_2);
x_2 = x_26;
goto _start;
}
case 9:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_29);
lean_dec_ref(x_2);
lean_inc(x_1);
x_30 = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(x_1, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get_size(x_29);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_1);
return x_30;
}
else
{
if (x_33 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_1);
return x_30;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_32);
x_36 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(x_1, x_29, x_34, x_35);
lean_dec_ref(x_29);
return x_36;
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec(x_1);
return x_30;
}
}
default: 
{
uint8_t x_37; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = 0;
return x_37;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
lean_inc(x_1);
x_21 = lean_register_option(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
x_4 = lean_box(0);
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00Lean_MessageData_formatAux_spec__3(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_2 = x_12;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(x_2, x_6, x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_formatAux___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static double _init_l_Lean_MessageData_formatAux___closed__10(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_formatRawGoal(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = l_Lean_MessageData_mkPPContext(x_1, x_10);
lean_dec(x_10);
lean_dec_ref(x_1);
x_12 = l_Lean_ppGoal(x_11, x_9);
return x_12;
}
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_2 = x_15;
x_3 = x_14;
goto _start;
}
case 4:
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
x_1 = x_17;
x_3 = x_18;
goto _start;
}
case 5:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = l_Lean_MessageData_formatAux(x_1, x_2, x_22);
x_24 = lean_nat_to_int(x_21);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = l_Lean_MessageData_formatAux(x_1, x_2, x_26);
x_28 = lean_nat_to_int(x_25);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
case 6:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_3);
x_31 = l_Lean_MessageData_formatAux(x_1, x_2, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
return x_33;
}
case 7:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc_ref(x_1);
x_37 = l_Lean_MessageData_formatAux(x_1, x_2, x_35);
x_38 = l_Lean_MessageData_formatAux(x_1, x_2, x_36);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_37);
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_41 = l_Lean_MessageData_formatAux(x_1, x_2, x_39);
x_42 = l_Lean_MessageData_formatAux(x_1, x_2, x_40);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
case 9:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_64; double x_65; double x_66; uint8_t x_67; 
x_44 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_46);
lean_dec_ref(x_3);
x_47 = lean_array_size(x_46);
x_48 = 0;
lean_inc(x_2);
lean_inc_ref(x_1);
x_49 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(x_1, x_2, x_47, x_48, x_46);
x_64 = lean_ctor_get(x_44, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_float(x_44, sizeof(void*)*2);
x_66 = lean_ctor_get_float(x_44, sizeof(void*)*2 + 8);
lean_dec_ref(x_44);
x_67 = l_Lean_Name_isAnonymous(x_64);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; double x_83; uint8_t x_84; 
x_68 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
x_69 = 1;
x_70 = l_Lean_Name_toString(x_64, x_69);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__7));
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_83 = lean_float_once(&l_Lean_MessageData_formatAux___closed__10, &l_Lean_MessageData_formatAux___closed__10_once, _init_l_Lean_MessageData_formatAux___closed__10);
x_84 = lean_float_beq(x_65, x_83);
if (x_84 == 0)
{
goto block_82;
}
else
{
if (x_67 == 0)
{
x_50 = x_74;
x_51 = lean_box(0);
goto block_63;
}
else
{
goto block_82;
}
}
block_82:
{
lean_object* x_75; lean_object* x_76; double x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__9));
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_float_sub(x_66, x_65);
x_78 = lean_float_to_string(x_77);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
x_50 = x_81;
x_51 = lean_box(0);
goto block_63;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_64);
lean_dec_ref(x_45);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = lean_array_to_list(x_49);
x_86 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
x_87 = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(x_85, x_86);
return x_87;
}
block_63:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = l_Lean_MessageData_formatAux(x_1, x_2, x_45);
x_53 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_obj_once(&l_Lean_MessageData_formatAux___closed__1, &l_Lean_MessageData_formatAux___closed__1_once, _init_l_Lean_MessageData_formatAux___closed__1);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_to_list(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
x_61 = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(x_59, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_88);
lean_dec_ref(x_3);
x_89 = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_107; 
x_107 = lean_box(0);
x_90 = x_107;
goto block_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = l_Lean_MessageData_mkPPContext(x_1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_90 = x_110;
goto block_106;
}
block_106:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_apply_2(x_88, x_90, lean_box(0));
x_92 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_91, x_89);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; 
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_3 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_92);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
x_96 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
x_97 = lean_unsigned_to_nat(310u);
x_98 = lean_unsigned_to_nat(8u);
x_99 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__13));
x_100 = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(x_91);
lean_dec(x_91);
x_101 = 1;
x_102 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_100, x_101);
x_103 = lean_string_append(x_99, x_102);
lean_dec_ref(x_102);
x_104 = l_mkPanicMessageWithDecl(x_95, x_96, x_97, x_98, x_103);
lean_dec_ref(x_103);
x_105 = l_panic___at___00Lean_MessageData_formatAux_spec__3(x_104);
return x_105;
}
}
}
default: 
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_111);
lean_dec_ref(x_3);
x_3 = x_111;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_array_uget_borrowed(x_5, x_4);
lean_inc(x_8);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_MessageData_formatAux(x_1, x_2, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_14 = lean_array_uset(x_11, x_4, x_9);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(x_1, x_2, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageData_formatAux(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_MessageData_format___closed__0));
x_5 = l_Lean_MessageData_formatAux(x_4, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_format(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = l_Lean_MessageData_format(x_1, x_3);
x_5 = l_Std_Format_defWidth;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_Format_pretty(x_4, x_5, x_6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_toString(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__7));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_fget_borrowed(x_1, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_13);
x_18 = l_Lean_MessageData_ofExpr(x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_4 = x_19;
goto block_8;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_13);
x_20 = l_Lean_MessageData_ofExpr(x_13);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_4 = x_21;
goto block_8;
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_instCoeArrayExpr___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_MessageData_ofFormat(x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
x_3 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
x_3 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
x_4 = l_Lean_MessageData_bracket(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_2);
x_3 = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
return x_5;
}
else
{
uint8_t x_6; 
lean_inc(x_4);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
lean_inc_ref(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_2);
x_8 = l_Lean_MessageData_joinSep(x_4, x_2);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
lean_inc_ref(x_2);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Lean_MessageData_joinSep(x_4, x_2);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_2 = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
x_4 = l_Lean_MessageData_joinSep(x_1, x_3);
x_5 = l_Lean_MessageData_sbracket(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(x_1);
x_3 = l_Lean_MessageData_ofList(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_7);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_18 = x_3;
} else {
 lean_dec_ref(x_3);
 x_18 = lean_box(0);
}
x_19 = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(7, 2, 0);
} else {
 x_20 = x_18;
 lean_ctor_set_tag(x_20, 7);
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(x_1);
x_26 = lean_array_mk(x_1);
x_27 = lean_array_pop(x_26);
x_28 = lean_array_to_list(x_27);
x_29 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
x_30 = l_Lean_MessageData_joinSep(x_28, x_29);
x_31 = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_30);
x_32 = l_List_getLast_x21___redArg(x_25, x_1);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_37 = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(x_1);
x_38 = lean_array_mk(x_1);
x_39 = lean_array_pop(x_38);
x_40 = lean_array_to_list(x_39);
x_41 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
x_42 = l_Lean_MessageData_joinSep(x_40, x_41);
x_43 = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_List_getLast_x21___redArg(x_37, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_46 = x_1;
} else {
 lean_dec_ref(x_1);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(7, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 7);
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_7);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_18 = x_3;
} else {
 lean_dec_ref(x_3);
 x_18 = lean_box(0);
}
x_19 = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(7, 2, 0);
} else {
 x_20 = x_18;
 lean_ctor_set_tag(x_20, 7);
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(x_1);
x_26 = lean_array_mk(x_1);
x_27 = lean_array_pop(x_26);
x_28 = lean_array_to_list(x_27);
x_29 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
x_30 = l_Lean_MessageData_joinSep(x_28, x_29);
x_31 = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_30);
x_32 = l_List_getLast_x21___redArg(x_25, x_1);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_37 = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(x_1);
x_38 = lean_array_mk(x_1);
x_39 = lean_array_pop(x_38);
x_40 = lean_array_to_list(x_39);
x_41 = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
x_42 = l_Lean_MessageData_joinSep(x_40, x_41);
x_43 = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_List_getLast_x21___redArg(x_37, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_46 = x_1;
} else {
 lean_dec_ref(x_1);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(7, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 7);
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_2 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_note___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
x_2 = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
x_2 = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___redArg(x_2, x_1, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_2 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_3 = l_Lean_instInhabitedPosition_default;
x_4 = lean_box(0);
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set(x_7, 4, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*5 + 1, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*5 + 2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedBaseMessage_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedBaseMessage_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedBaseMessage_default___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
x_9 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
x_12 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
x_18 = l_Lean_instToJsonPosition_toJson(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
x_22 = l_Option_toJson___redArg(x_11, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
x_26 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_26, 0, x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
x_29 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
x_30 = l_Lean_instToJsonMessageSeverity_toJson(x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_15);
x_33 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
x_34 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_34, 0, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
x_37 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_9);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_15);
x_41 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
x_42 = lean_apply_1(x_1, x_10);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_32);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
x_54 = lean_obj_once(&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10, &l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_once, _init_l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10);
x_55 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), x_53, x_52, x_54);
x_56 = l_Lean_Json_mkObj(x_55);
return x_56;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToJsonBaseMessage_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
x_4 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(x_2);
x_5 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_ctor_set_tag(x_5, 0);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec_ref(x_5);
x_18 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
x_19 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
x_20 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(x_2);
x_21 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_ctor_set_tag(x_21, 0);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec_ref(x_21);
x_34 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(x_2);
x_35 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_19, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_44; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_ctor_set_tag(x_35, 0);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec_ref(x_35);
x_48 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
x_49 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(x_2);
x_50 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_59; 
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
lean_ctor_set_tag(x_50, 0);
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
x_63 = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
x_64 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(x_2);
x_65 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_63, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_74; 
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_ctor_set_tag(x_65, 0);
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
lean_dec_ref(x_65);
x_78 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(x_2);
x_79 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_48, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_83);
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_88; 
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
lean_ctor_set_tag(x_79, 0);
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
lean_dec(x_79);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
lean_dec_ref(x_79);
x_92 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(x_2);
x_93 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_3, x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_91);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_102; 
lean_dec(x_91);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
lean_ctor_set_tag(x_93, 0);
return x_93;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
lean_dec(x_93);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
lean_dec_ref(x_93);
x_106 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
x_107 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_1, x_106);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_105);
lean_dec(x_91);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
lean_ctor_set(x_107, 0, x_111);
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
else
{
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_116; 
lean_dec(x_105);
lean_dec(x_91);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_17);
x_116 = !lean_is_exclusive(x_107);
if (x_116 == 0)
{
lean_ctor_set_tag(x_107, 0);
return x_107;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
lean_dec(x_107);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_107);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_107, 0);
x_121 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_121, 0, x_17);
lean_ctor_set(x_121, 1, x_33);
lean_ctor_set(x_121, 2, x_47);
lean_ctor_set(x_121, 3, x_105);
lean_ctor_set(x_121, 4, x_120);
x_122 = lean_unbox(x_62);
lean_dec(x_62);
lean_ctor_set_uint8(x_121, sizeof(void*)*5, x_122);
x_123 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_121, sizeof(void*)*5 + 1, x_123);
x_124 = lean_unbox(x_91);
lean_dec(x_91);
lean_ctor_set_uint8(x_121, sizeof(void*)*5 + 2, x_124);
lean_ctor_set(x_107, 0, x_121);
return x_107;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_107, 0);
lean_inc(x_125);
lean_dec(x_107);
x_126 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_126, 0, x_17);
lean_ctor_set(x_126, 1, x_33);
lean_ctor_set(x_126, 2, x_47);
lean_ctor_set(x_126, 3, x_105);
lean_ctor_set(x_126, 4, x_125);
x_127 = lean_unbox(x_62);
lean_dec(x_62);
lean_ctor_set_uint8(x_126, sizeof(void*)*5, x_127);
x_128 = lean_unbox(x_77);
lean_dec(x_77);
lean_ctor_set_uint8(x_126, sizeof(void*)*5 + 1, x_128);
x_129 = lean_unbox(x_91);
lean_dec(x_91);
lean_ctor_set_uint8(x_126, sizeof(void*)*5 + 2, x_129);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_126);
return x_130;
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
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instFromJsonBaseMessage_fromJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_instToJsonPosition_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 2);
x_11 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
x_18 = l_Lean_instToJsonPosition_toJson(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
x_22 = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
x_26 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_26, 0, x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
x_29 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
x_30 = l_Lean_instToJsonMessageSeverity_toJson(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_15);
x_33 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
x_34 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_34, 0, x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
x_37 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_11);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_15);
x_41 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_12);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_15);
x_45 = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
x_46 = 1;
x_47 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_4, x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_15);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_32);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_20);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_obj_once(&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10, &l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_once, _init_l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10);
x_61 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(x_59, x_60);
x_62 = l_Lean_Json_mkObj(x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_63, sizeof(void*)*5);
x_69 = lean_ctor_get_uint8(x_63, sizeof(void*)*5 + 1);
x_70 = lean_ctor_get_uint8(x_63, sizeof(void*)*5 + 2);
x_71 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_63, 4);
lean_inc(x_72);
lean_dec_ref(x_63);
x_73 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_65);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
x_79 = l_Lean_instToJsonPosition_toJson(x_66);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
x_83 = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(x_67);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
x_86 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
x_87 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_87, 0, x_68);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_76);
x_90 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
x_91 = l_Lean_instToJsonMessageSeverity_toJson(x_69);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_76);
x_94 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
x_95 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_95, 0, x_70);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_76);
x_98 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_71);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_76);
x_102 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_72);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_76);
x_106 = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
x_107 = 1;
x_108 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_64, x_107);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_76);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_76);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_97);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_93);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_89);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_85);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_81);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_77);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_obj_once(&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10, &l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_once, _init_l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10);
x_122 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(x_120, x_121);
x_123 = l_Lean_Json_mkObj(x_122);
return x_123;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_instFromJsonPosition_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getBool_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_instFromJsonMessageSeverity_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Name_fromJson_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_instFromJsonPosition_fromJson(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
x_2 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(x_1);
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(x_1);
x_31 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec_ref(x_31);
x_44 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_54; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
lean_dec_ref(x_45);
x_58 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(x_1);
x_59 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(x_1, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_68; 
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
lean_ctor_set_tag(x_59, 0);
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
lean_dec_ref(x_59);
x_72 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(x_1);
x_73 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(x_1, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_82; 
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
lean_ctor_set_tag(x_73, 0);
return x_73;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_73, 0);
lean_inc(x_85);
lean_dec_ref(x_73);
x_86 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
x_91 = lean_string_append(x_90, x_89);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_96; 
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
lean_ctor_set_tag(x_87, 0);
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
lean_dec_ref(x_87);
x_100 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(x_1);
x_101 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(x_1, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
lean_ctor_set(x_101, 0, x_105);
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
else
{
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_110; 
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
lean_ctor_set_tag(x_101, 0);
return x_101;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
lean_dec(x_101);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_dec_ref(x_101);
x_114 = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
x_115 = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(x_1, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_119);
return x_115;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_124; 
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
x_124 = !lean_is_exclusive(x_115);
if (x_124 == 0)
{
lean_ctor_set_tag(x_115, 0);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_115, 0);
lean_inc(x_125);
lean_dec(x_115);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_115);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_115, 0);
x_129 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_129, 0, x_15);
lean_ctor_set(x_129, 1, x_29);
lean_ctor_set(x_129, 2, x_43);
lean_ctor_set(x_129, 3, x_99);
lean_ctor_set(x_129, 4, x_113);
x_130 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_129, sizeof(void*)*5, x_130);
x_131 = lean_unbox(x_71);
lean_dec(x_71);
lean_ctor_set_uint8(x_129, sizeof(void*)*5 + 1, x_131);
x_132 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_129, sizeof(void*)*5 + 2, x_132);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_115, 0, x_133);
return x_115;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_115, 0);
lean_inc(x_134);
lean_dec(x_115);
x_135 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_135, 0, x_15);
lean_ctor_set(x_135, 1, x_29);
lean_ctor_set(x_135, 2, x_43);
lean_ctor_set(x_135, 3, x_99);
lean_ctor_set(x_135, 4, x_113);
x_136 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_135, sizeof(void*)*5, x_136);
x_137 = lean_unbox(x_71);
lean_dec(x_71);
lean_ctor_set_uint8(x_135, sizeof(void*)*5 + 1, x_137);
x_138 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_135, sizeof(void*)*5 + 2, x_138);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_134);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_kindOfErrorName(x_2);
x_4 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(x_2);
x_9 = l_Lean_Name_isAnonymous(x_4);
if (x_9 == 0)
{
x_5 = x_9;
goto block_8;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
x_11 = lean_string_dec_eq(x_3, x_10);
x_5 = x_11;
goto block_8;
}
block_8:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Name_str___override(x_4, x_3);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_7 = lean_box(0);
return x_7;
}
}
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(x_12);
x_15 = l_Lean_Name_num___override(x_14, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_MessageData_stripNestedTags(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Lean_MessageData_stripNestedTags(x_6);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
case 4:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_MessageData_stripNestedTags(x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_MessageData_stripNestedTags(x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
case 8:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(x_17);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(x_19);
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_errorNameOfKind_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_kind(x_1);
x_3 = l_Lean_errorNameOfKind_x3f(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageData_errorName_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_Lean_MessageData_errorName_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Message_errorName_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_MessageData_ofFormat(x_5);
lean_ctor_set(x_2, 4, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; uint8_t x_8; uint32_t x_9; lean_object* x_13; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_43; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_26, sizeof(void*)*5 + 1);
x_32 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_26, 4);
lean_inc(x_33);
lean_dec_ref(x_26);
if (x_2 == 0)
{
lean_object* x_50; 
lean_dec(x_30);
x_50 = lean_box(0);
x_43 = x_50;
goto block_49;
}
else
{
x_43 = x_30;
goto block_49;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
block_12:
{
uint32_t x_10; uint8_t x_11; 
x_10 = 10;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_3 = x_7;
goto block_6;
}
else
{
if (x_8 == 0)
{
return x_7;
}
else
{
x_3 = x_7;
goto block_6;
}
}
}
block_25:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_string_utf8_byte_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_14);
x_18 = l_String_Slice_Pos_prev_x3f(x_17, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint32_t x_19; 
lean_dec_ref(x_17);
x_19 = 65;
x_7 = x_13;
x_8 = x_16;
x_9 = x_19;
goto block_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_String_Slice_Pos_get_x3f(x_17, x_20);
lean_dec(x_20);
lean_dec_ref(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint32_t x_22; 
x_22 = 65;
x_7 = x_13;
x_8 = x_16;
x_9 = x_22;
goto block_12;
}
else
{
lean_object* x_23; uint32_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_unbox_uint32(x_23);
lean_dec(x_23);
x_7 = x_13;
x_8 = x_16;
x_9 = x_24;
goto block_12;
}
}
}
else
{
x_3 = x_13;
goto block_6;
}
}
block_42:
{
switch (x_31) {
case 0:
{
lean_dec(x_34);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
x_13 = x_35;
goto block_25;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
x_37 = l_Lean_errorNameOfKind_x3f(x_27);
lean_dec(x_27);
x_38 = l_Lean_mkErrorStringWithPos(x_28, x_29, x_35, x_34, x_36, x_37);
lean_dec_ref(x_35);
x_13 = x_38;
goto block_25;
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
x_40 = l_Lean_errorNameOfKind_x3f(x_27);
lean_dec(x_27);
x_41 = l_Lean_mkErrorStringWithPos(x_28, x_29, x_35, x_34, x_39, x_40);
lean_dec_ref(x_35);
x_13 = x_41;
goto block_25;
}
}
}
block_49:
{
lean_object* x_44; uint8_t x_45; 
x_44 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_45 = lean_string_dec_eq(x_32, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
x_47 = lean_string_append(x_32, x_46);
x_48 = lean_string_append(x_47, x_33);
lean_dec(x_33);
x_34 = x_43;
x_35 = x_48;
goto block_42;
}
else
{
lean_dec_ref(x_32);
x_34 = x_43;
x_35 = x_33;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_SerialMessage_toString(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l_Lean_SerialMessage_toString(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_Lean_MessageData_kind(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Message_kind(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_Lean_MessageData_isTrace(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Message_isTrace(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_MessageData_toString(x_4);
lean_ctor_set(x_1, 4, x_5);
x_6 = l_Lean_MessageData_kind(x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_15);
x_16 = l_Lean_MessageData_toString(x_15);
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_13);
x_18 = l_Lean_MessageData_kind(x_15);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Message_serialize(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; uint32_t x_17; lean_object* x_21; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_44; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec_ref(x_1);
lean_inc(x_9);
x_10 = l_Lean_MessageData_toString(x_9);
x_34 = l_Lean_MessageData_kind(x_9);
lean_dec(x_9);
if (x_2 == 0)
{
lean_object* x_51; 
lean_dec(x_6);
x_51 = lean_box(0);
x_44 = x_51;
goto block_50;
}
else
{
x_44 = x_6;
goto block_50;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
x_13 = lean_string_append(x_11, x_12);
return x_13;
}
block_20:
{
uint32_t x_18; uint8_t x_19; 
x_18 = 10;
x_19 = lean_uint32_dec_eq(x_17, x_18);
if (x_19 == 0)
{
x_11 = x_15;
goto block_14;
}
else
{
if (x_16 == 0)
{
return x_15;
}
else
{
x_11 = x_15;
goto block_14;
}
}
}
block_33:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_string_utf8_byte_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_21);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
x_26 = l_String_Slice_Pos_prev_x3f(x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint32_t x_27; 
lean_dec_ref(x_25);
x_27 = 65;
x_15 = x_21;
x_16 = x_24;
x_17 = x_27;
goto block_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_String_Slice_Pos_get_x3f(x_25, x_28);
lean_dec(x_28);
lean_dec_ref(x_25);
if (lean_obj_tag(x_29) == 0)
{
uint32_t x_30; 
x_30 = 65;
x_15 = x_21;
x_16 = x_24;
x_17 = x_30;
goto block_20;
}
else
{
lean_object* x_31; uint32_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_15 = x_21;
x_16 = x_24;
x_17 = x_32;
goto block_20;
}
}
}
else
{
x_11 = x_21;
goto block_14;
}
}
block_43:
{
switch (x_7) {
case 0:
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = x_36;
goto block_33;
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
x_38 = l_Lean_errorNameOfKind_x3f(x_34);
lean_dec(x_34);
x_39 = l_Lean_mkErrorStringWithPos(x_4, x_5, x_36, x_35, x_37, x_38);
lean_dec_ref(x_36);
x_21 = x_39;
goto block_33;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
x_41 = l_Lean_errorNameOfKind_x3f(x_34);
lean_dec(x_34);
x_42 = l_Lean_mkErrorStringWithPos(x_4, x_5, x_36, x_35, x_40, x_41);
lean_dec_ref(x_36);
x_21 = x_42;
goto block_33;
}
}
}
block_50:
{
lean_object* x_45; uint8_t x_46; 
x_45 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_46 = lean_string_dec_eq(x_8, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
x_48 = lean_string_append(x_8, x_47);
x_49 = lean_string_append(x_48, x_10);
lean_dec_ref(x_10);
x_35 = x_44;
x_36 = x_49;
goto block_43;
}
else
{
lean_dec_ref(x_8);
x_35 = x_44;
x_36 = x_10;
goto block_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Message_toString(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec_ref(x_1);
lean_inc(x_10);
x_11 = l_Lean_MessageData_toString(x_10);
x_12 = l_Lean_MessageData_kind(x_10);
lean_dec(x_10);
x_13 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
x_19 = l_Lean_instToJsonPosition_toJson(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
x_23 = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
x_27 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_27, 0, x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
x_30 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
x_31 = l_Lean_instToJsonMessageSeverity_toJson(x_7);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
x_34 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
x_35 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_35, 0, x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_16);
x_42 = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_11);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_16);
x_46 = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
x_47 = 1;
x_48 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_12, x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_29);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_25);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_21);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_17);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_obj_once(&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10, &l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_once, _init_l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10);
x_62 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(x_60, x_61);
x_63 = l_Lean_Json_mkObj(x_62);
return x_63;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Message_toJson(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageLog_default;
return x_1;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_MessageLog_empty___closed__0, &l_Lean_MessageLog_empty___closed__0_once, _init_l_Lean_MessageLog_empty___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__2(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_MessageLog_empty___closed__0, &l_Lean_MessageLog_empty___closed__0_once, _init_l_Lean_MessageLog_empty___closed__0);
x_4 = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_MessageLog_empty___closed__3, &l_Lean_MessageLog_empty___closed__3_once, _init_l_Lean_MessageLog_empty___closed__3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_msgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_PersistentArray_append___redArg(x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_isEmpty___redArg(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasUnreported(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentArray_push___redArg(x_4, x_1);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_9 = l_Lean_PersistentArray_push___redArg(x_7, x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_2, x_6);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_5);
x_11 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_1, x_2, x_8);
x_12 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_11, x_9);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(x_1, x_13);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_3);
lean_dec(x_5);
x_16 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_1, x_2, x_9);
x_17 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_6, x_7, x_8, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_23 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_2, x_19);
switch (x_23) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_24 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_1, x_2, x_21);
x_25 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_19, x_20, x_24, x_22);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_20);
x_27 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(x_1, x_26);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_30 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_1, x_2, x_22);
x_31 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_19, x_20, x_21, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_box(0);
x_33 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(x_1, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_3);
lean_ctor_set(x_36, 4, x_3);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(x_1, x_5);
x_8 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_4, x_3, x_7);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = l_Lean_PersistentArray_append___redArg(x_3, x_7);
lean_dec_ref(x_7);
x_11 = l_Lean_PersistentArray_append___redArg(x_4, x_8);
lean_dec_ref(x_8);
x_12 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(x_5, x_9);
lean_ctor_set(x_2, 2, x_12);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = l_Lean_PersistentArray_append___redArg(x_3, x_13);
lean_dec_ref(x_13);
x_17 = l_Lean_PersistentArray_append___redArg(x_4, x_14);
lean_dec_ref(x_14);
x_18 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(x_5, x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_7 = 1;
if (x_6 == 2)
{
return x_7;
}
else
{
if (x_4 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(x_2, x_6, x_7);
return x_8;
}
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
return x_12;
}
else
{
if (x_12 == 0)
{
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_11);
x_15 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(x_9, x_13, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
return x_6;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
if (x_7 == 0)
{
return x_4;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(x_3, x_8, x_9);
return x_10;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
x_8 = 1;
if (x_7 == 2)
{
return x_8;
}
else
{
if (x_1 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
if (x_6 == 0)
{
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_13 == 0)
{
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_12);
x_16 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(x_1, x_10, x_14, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(x_1, x_4, x_9, x_10);
return x_11;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(x_4, x_3);
return x_5;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageLog_hasErrors(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_append___redArg(x_3, x_4);
lean_dec_ref(x_4);
x_6 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = l_Lean_PersistentArray_append___redArg(x_7, x_8);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
if (x_10 == 2)
{
uint8_t x_22; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_5, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_dec(x_27);
x_28 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 1, x_28);
x_16 = x_5;
goto block_21;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_8);
lean_ctor_set(x_30, 3, x_12);
lean_ctor_set(x_30, 4, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 2, x_11);
x_16 = x_30;
goto block_21;
}
}
else
{
x_16 = x_5;
goto block_21;
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_4, x_5, x_3);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_8, x_9, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(x_14, x_15, x_13);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(x_18, x_19, x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(x_3);
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(x_6, x_7, x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_usize(x_1, 4);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_14 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(x_9);
x_15 = lean_array_size(x_10);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(x_15, x_16, x_10);
x_18 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set_usize(x_18, 4, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(x_4);
x_8 = l_Lean_NameSet_empty;
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(x_9);
x_11 = l_Lean_NameSet_empty;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
if (x_10 == 2)
{
uint8_t x_22; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_5, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_dec(x_27);
x_28 = 0;
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 1, x_28);
x_16 = x_5;
goto block_21;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_8);
lean_ctor_set(x_30, 3, x_12);
lean_ctor_set(x_30, 4, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 2, x_11);
x_16 = x_30;
goto block_21;
}
}
else
{
x_16 = x_5;
goto block_21;
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_4, x_5, x_3);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_8, x_9, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(x_14, x_15, x_13);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(x_18, x_19, x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(x_3);
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(x_6, x_7, x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_usize(x_1, 4);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_14 = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(x_9);
x_15 = lean_array_size(x_10);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(x_15, x_16, x_10);
x_18 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set_usize(x_18, 4, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(x_4);
x_8 = l_Lean_NameSet_empty;
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(x_9);
x_11 = l_Lean_NameSet_empty;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = l_Lean_PersistentArray_push___redArg(x_4, x_11);
x_5 = x_13;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(x_3, x_8, x_9, x_2);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(x_3, x_11, x_12, x_2);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
return x_2;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
if (x_17 == 0)
{
return x_2;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_16);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_14, x_19, x_20, x_2);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_14, x_22, x_23, x_2);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(x_6, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
x_7 = lean_usize_shift_right(x_2, x_3);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_borrowed(x_6, x_5, x_8);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_9, x_13, x_15, x_4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
if (x_20 == 0)
{
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(x_5, x_22, x_23, x_16);
return x_24;
}
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_of_nat(x_19);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(x_5, x_25, x_26, x_16);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_usize_to_nat(x_2);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_29);
return x_4;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
if (x_31 == 0)
{
lean_dec(x_29);
return x_4;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = lean_usize_of_nat(x_30);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_28, x_33, x_34, x_4);
return x_35;
}
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = lean_usize_of_nat(x_30);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_28, x_36, x_37, x_4);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_usize(x_1, 4);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_nat_dec_le(x_9, x_3);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_usize_of_nat(x_3);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(x_6, x_11, x_8, x_2);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
return x_12;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
return x_12;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_7, x_16, x_17, x_12);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_7, x_19, x_20, x_12);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_nat_sub(x_3, x_9);
x_23 = lean_array_get_size(x_7);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_22);
return x_2;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec(x_22);
return x_2;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = lean_usize_of_nat(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_7, x_26, x_27, x_2);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = lean_usize_of_nat(x_23);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_7, x_29, x_30, x_2);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(x_32, x_2);
x_35 = lean_array_get_size(x_33);
x_36 = lean_nat_dec_lt(x_4, x_35);
if (x_36 == 0)
{
return x_34;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
if (x_36 == 0)
{
return x_34;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_35);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_33, x_38, x_39, x_34);
return x_40;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(x_33, x_41, x_42, x_34);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(x_5, x_3, x_2);
lean_dec_ref(x_5);
x_9 = l_Lean_NameSet_empty;
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(x_10, x_3, x_2);
lean_dec_ref(x_10);
x_12 = l_Lean_NameSet_empty;
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 1);
if (x_12 == 1)
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = l_Lean_PersistentArray_push___redArg(x_4, x_11);
x_5 = x_13;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(x_3, x_8, x_9, x_2);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(x_3, x_11, x_12, x_2);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
return x_2;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
if (x_17 == 0)
{
return x_2;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_16);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_14, x_19, x_20, x_2);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_14, x_22, x_23, x_2);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(x_6, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
x_7 = lean_usize_shift_right(x_2, x_3);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_borrowed(x_6, x_5, x_8);
x_10 = 1;
x_11 = lean_usize_shift_left(x_10, x_3);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = 5;
x_15 = lean_usize_sub(x_3, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(x_9, x_13, x_15, x_4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
if (x_20 == 0)
{
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(x_5, x_22, x_23, x_16);
return x_24;
}
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_usize_of_nat(x_19);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(x_5, x_25, x_26, x_16);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_usize_to_nat(x_2);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_29);
return x_4;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
if (x_31 == 0)
{
lean_dec(x_29);
return x_4;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = lean_usize_of_nat(x_30);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_28, x_33, x_34, x_4);
return x_35;
}
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = lean_usize_of_nat(x_30);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_28, x_36, x_37, x_4);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_usize(x_1, 4);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_nat_dec_le(x_9, x_3);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_usize_of_nat(x_3);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(x_6, x_11, x_8, x_2);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
return x_12;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
return x_12;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_7, x_16, x_17, x_12);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_7, x_19, x_20, x_12);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_nat_sub(x_3, x_9);
x_23 = lean_array_get_size(x_7);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_22);
return x_2;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec(x_22);
return x_2;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = lean_usize_of_nat(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_7, x_26, x_27, x_2);
return x_28;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = lean_usize_of_nat(x_23);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_7, x_29, x_30, x_2);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(x_32, x_2);
x_35 = lean_array_get_size(x_33);
x_36 = lean_nat_dec_lt(x_4, x_35);
if (x_36 == 0)
{
return x_34;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
if (x_36 == 0)
{
return x_34;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_35);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_33, x_38, x_39, x_34);
return x_40;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(x_33, x_41, x_42, x_34);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(x_5, x_3, x_2);
lean_dec_ref(x_5);
x_9 = l_Lean_NameSet_empty;
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(x_10, x_3, x_2);
lean_dec_ref(x_10);
x_12 = l_Lean_NameSet_empty;
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentArray_forM___redArg(x_1, x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageLog_forM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_toList___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toList(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_PersistentArray_toArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MessageLog_toArray(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_MessageData_nestD(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofExpr(x_1);
x_3 = l_Lean_indentD(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_format(x_11, x_13);
x_15 = l_Std_Format_defWidth;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Std_Format_pretty(x_14, x_15, x_16, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
x_10 = lean_string_utf8_get_fast(x_4, x_9);
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_utf8_next_fast(x_4, x_9);
lean_dec(x_9);
x_14 = lean_nat_sub(x_13, x_5);
x_2 = x_14;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_9);
return x_12;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(x_1, x_2, x_4);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_16; uint8_t x_17; 
x_5 = l_Lean_MessageData_ofExpr(x_1);
lean_inc_ref(x_5);
x_6 = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(x_3, x_5);
x_16 = lean_string_length(x_6);
x_17 = lean_nat_dec_lt(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_string_utf8_byte_size(x_6);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(x_20);
lean_dec_ref(x_20);
x_7 = x_21;
goto block_15;
}
else
{
lean_dec_ref(x_6);
x_7 = x_17;
goto block_15;
}
block_15:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_indentD(x_5);
x_13 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_inlineExpr___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
x_5 = l_Lean_MessageData_ofExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_inlineExpr___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_MessageData_lazy(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_5);
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_14; uint8_t x_15; 
x_5 = l_Lean_MessageData_ofExpr(x_1);
lean_inc_ref(x_5);
x_6 = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(x_3, x_5);
x_14 = lean_string_length(x_6);
x_15 = lean_nat_dec_lt(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_6);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(x_18);
lean_dec_ref(x_18);
x_7 = x_19;
goto block_13;
}
else
{
lean_dec_ref(x_6);
x_7 = x_15;
goto block_13;
}
block_13:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_indentD(x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_inlineExprTrailing___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
x_5 = l_Lean_MessageData_ofExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_inlineExprTrailing___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_MessageData_lazy(x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_aquote___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_aquote___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
x_4 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
x_3 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
x_6 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__3, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__3_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__3);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_4);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addMessageContextPartial___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_6);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_4);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addMessageContextFull___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_sub(x_19, x_18);
x_21 = lean_nat_dec_eq(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint32_t x_22; uint32_t x_23; uint8_t x_24; 
x_22 = 10;
x_23 = lean_string_utf8_get_fast(x_1, x_17);
x_24 = lean_uint32_dec_eq(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_string_utf8_next_fast(x_1, x_17);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_25);
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_string_utf8_next_fast(x_1, x_17);
x_28 = lean_nat_sub(x_27, x_17);
x_29 = lean_nat_add(x_17, x_28);
lean_dec(x_28);
x_30 = l_String_Slice_subslice_x21(x_2, x_16, x_17);
lean_inc(x_29);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set(x_4, 0, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_6 = x_4;
x_7 = x_31;
x_8 = x_32;
goto block_14;
}
}
else
{
lean_object* x_33; 
lean_free_object(x_4);
lean_dec(x_17);
x_33 = lean_box(1);
lean_inc(x_3);
x_6 = x_33;
x_7 = x_16;
x_8 = x_3;
goto block_14;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_nat_sub(x_37, x_36);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint32_t x_40; uint32_t x_41; uint8_t x_42; 
x_40 = 10;
x_41 = lean_string_utf8_get_fast(x_1, x_35);
x_42 = lean_uint32_dec_eq(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_string_utf8_next_fast(x_1, x_35);
lean_dec(x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
x_4 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_string_utf8_next_fast(x_1, x_35);
x_47 = lean_nat_sub(x_46, x_35);
x_48 = lean_nat_add(x_35, x_47);
lean_dec(x_47);
x_49 = l_String_Slice_subslice_x21(x_2, x_34, x_35);
lean_inc(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
x_6 = x_50;
x_7 = x_51;
x_8 = x_52;
goto block_14;
}
}
else
{
lean_object* x_53; 
lean_dec(x_35);
x_53 = lean_box(1);
lean_inc(x_3);
x_6 = x_53;
x_7 = x_34;
x_8 = x_3;
goto block_14;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_string_utf8_extract(x_1, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = lean_array_push(x_5, x_11);
x_4 = x_6;
x_5 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_stringToMessageData___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(x_4);
x_6 = lean_obj_once(&l_Lean_stringToMessageData___closed__0, &l_Lean_stringToMessageData___closed__0_once, _init_l_Lean_stringToMessageData___closed__0);
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(x_1, x_4, x_3, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_8 = lean_array_to_list(x_7);
x_9 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_10 = l_Lean_MessageData_joinSep(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_2);
lean_closure_set(x_3, 4, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataOfToFormat___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToMessageDataTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___redArg(x_1, x_2, x_3);
x_5 = l_Lean_MessageData_ofList(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_to_list(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___redArg(x_1, x_3, x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
lean_inc_ref(x_5);
lean_ctor_set(x_1, 1, x_10);
x_11 = lean_array_fget(x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
x_12 = lean_array_push(x_2, x_11);
x_13 = lean_apply_3(x_3, x_1, x_12, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
lean_inc_ref(x_14);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
x_21 = lean_array_fget(x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
x_22 = lean_array_push(x_2, x_21);
x_23 = lean_apply_3(x_3, x_20, x_22, lean_box(0));
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_obj_once(&l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0, &l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0_once, _init_l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0);
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(x_1, x_3, x_4);
x_6 = lean_array_to_list(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___redArg(x_2, x_6, x_7);
x_9 = l_Lean_MessageData_ofList(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToMessageDataSubarray___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
x_9 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_1(x_2, x_6);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_paren(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_apply_1(x_1, x_14);
x_17 = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_1(x_2, x_15);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_MessageData_paren(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_10, x_13);
x_15 = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
x_16 = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_addMacroScope(x_8, x_16, x_9);
x_18 = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(x_14);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
x_21 = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_addMacroScope(x_8, x_21, x_9);
x_23 = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_inc_ref(x_24);
x_25 = l_Lean_TSyntax_expandInterpolatedStr(x_12, x_19, x_24, x_24, x_2, x_3);
lean_dec(x_12);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_toMessageList___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_to_list(x_1);
x_3 = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
x_4 = l_Lean_MessageData_joinSep(x_2, x_3);
x_5 = l_Lean_indentD(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_elab_environment_of_kernel_env(x_1);
x_6 = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
x_5 = l_Lean_MessageData_ofName(x_2);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentExpr(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_indentExpr(x_3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
x_3 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_7 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
x_8 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_4, x_6, x_2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_15 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
x_16 = l_Lean_MessageData_ofName(x_13);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_12, x_14, x_2, x_19);
return x_20;
}
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_25 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
x_26 = 1;
x_27 = l_Lean_MessageData_ofConstName(x_23, x_26);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
x_28 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_22, x_24, x_2, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_34 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
x_35 = 1;
x_36 = l_Lean_MessageData_ofConstName(x_32, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_31, x_33, x_2, x_39);
return x_40;
}
}
case 2:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_43);
lean_dec_ref(x_1);
x_44 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch (lean_obj_tag(x_42)) {
case 1:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_45);
lean_dec_ref(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_43, x_47, x_48);
x_50 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_41, x_44, x_2, x_49);
return x_50;
}
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_51);
lean_dec_ref(x_42);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_Kernel_Exception_toMessageData___lam__0(x_43, x_53, x_54);
x_56 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_41, x_44, x_2, x_55);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_43);
lean_dec(x_42);
x_57 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
x_58 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_41, x_44, x_2, x_57);
return x_58;
}
}
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec_ref(x_1);
x_61 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_62 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
x_63 = 1;
x_64 = l_Lean_MessageData_ofConstName(x_60, x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_59, x_61, x_2, x_67);
return x_68;
}
case 4:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_71);
lean_dec_ref(x_1);
x_72 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_73 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
x_74 = 1;
x_75 = l_Lean_MessageData_ofConstName(x_70, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_indentExpr(x_71);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_69, x_72, x_2, x_80);
return x_81;
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_84);
lean_dec_ref(x_1);
x_85 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
x_86 = l_Lean_indentExpr(x_84);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_82, x_83, x_2, x_87);
return x_88;
}
case 6:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_91);
lean_dec_ref(x_1);
x_92 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
x_93 = l_Lean_indentExpr(x_91);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_89, x_90, x_2, x_94);
return x_95;
}
case 7:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
lean_dec_ref(x_1);
x_99 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
x_100 = l_Lean_MessageData_ofName(x_98);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_96, x_97, x_2, x_103);
return x_104;
}
case 8:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_107);
lean_dec_ref(x_1);
x_108 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
x_109 = l_Lean_indentExpr(x_107);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_105, x_106, x_2, x_110);
return x_111;
}
case 9:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_116);
lean_dec_ref(x_1);
x_117 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
x_118 = l_Lean_indentExpr(x_114);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_indentExpr(x_116);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_indentExpr(x_115);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_112, x_113, x_2, x_127);
return x_128;
}
case 10:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_131);
lean_dec_ref(x_1);
x_132 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
x_133 = l_Lean_indentExpr(x_131);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_129, x_130, x_2, x_134);
return x_135;
}
case 11:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_138);
lean_dec_ref(x_1);
x_139 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
x_140 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
x_141 = 1;
x_142 = l_Lean_MessageData_ofConstName(x_137, x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_indentExpr(x_138);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(x_136, x_139, x_2, x_147);
return x_148;
}
case 12:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_2);
x_149 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_149);
lean_dec_ref(x_1);
x_150 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
x_151 = l_Lean_stringToMessageData(x_149);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
case 13:
{
lean_object* x_153; 
lean_dec_ref(x_2);
x_153 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return x_153;
}
case 14:
{
lean_object* x_154; 
lean_dec_ref(x_2);
x_154 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return x_154;
}
case 15:
{
lean_object* x_155; 
lean_dec_ref(x_2);
x_155 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return x_155;
}
default: 
{
lean_object* x_156; 
lean_dec_ref(x_2);
x_156 = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_float_once(&l_Lean_MessageData_formatAux___closed__10, &l_Lean_MessageData_formatAux___closed__10_once, _init_l_Lean_MessageData_formatAux___closed__10);
x_5 = 1;
x_6 = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
x_7 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set_float(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_float(x_7, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 16, x_5);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_obj_once(&l_Lean_stringToMessageData___closed__0, &l_Lean_stringToMessageData___closed__0_once, _init_l_Lean_stringToMessageData___closed__0);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_toTraceElem___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedMessageSeverity_default = _init_l_Lean_instInhabitedMessageSeverity_default();
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instInhabitedMessageData_default = _init_l_Lean_instInhabitedMessageData_default();
lean_mark_persistent(l_Lean_instInhabitedMessageData_default);
l_Lean_instInhabitedMessageData = _init_l_Lean_instInhabitedMessageData();
lean_mark_persistent(l_Lean_instInhabitedMessageData);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
res = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_MessageData_maxTraceChildren = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_MessageData_maxTraceChildren);
lean_dec_ref(res);
l_Lean_instInhabitedMessageLog_default = _init_l_Lean_instInhabitedMessageLog_default();
lean_mark_persistent(l_Lean_instInhabitedMessageLog_default);
l_Lean_instInhabitedMessageLog = _init_l_Lean_instInhabitedMessageLog();
lean_mark_persistent(l_Lean_instInhabitedMessageLog);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
