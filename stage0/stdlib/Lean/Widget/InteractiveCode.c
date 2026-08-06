// Lean compiler output
// Module: Lean.Widget.InteractiveCode
// Imports: public import Lean.Widget.TaggedText public import Lean.Widget.Basic
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
extern lean_object* l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_empty(lean_object*);
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_pp_raw;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "wasChanged"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__1 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value;
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "willChange"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__2 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__3 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value;
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "wasDeleted"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__4 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__5 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value;
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "willDelete"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__6 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__7 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value;
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "wasInserted"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__8 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__9 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value;
static const lean_string_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "willInsert"};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__10 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value;
static const lean_ctor_object l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value)}};
static const lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___closed__11 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonDiffTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonDiffTag_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonDiffTag___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonDiffTag = (const lean_object*)&l_Lean_Widget_instToJsonDiffTag___closed__0_value;
static const lean_string_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value;
static const lean_string_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value)}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonDiffTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonDiffTag_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonDiffTag___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonDiffTag = (const lean_object*)&l_Lean_Widget_instFromJsonDiffTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "subexprPos"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "diffStatus"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1 = (const lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value),((lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2 = (const lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo = (const lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0 = (const lean_object*)&l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_ppExprTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_ppExprTagged___closed__0 = (const lean_object*)&l_Lean_Widget_ppExprTagged___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_x_boxed_9_; lean_object* v_res_10_; 
v_x_boxed_9_ = lean_unbox(v_x_8_);
v_res_10_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg(lean_object* v_k_11_){
_start:
{
lean_inc(v_k_11_);
return v_k_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(lean_object* v_k_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_12_);
lean_dec(v_k_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, uint8_t v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_inc(v_k_18_);
return v_k_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
uint8_t v_t_boxed_24_; lean_object* v_res_25_; 
v_t_boxed_24_ = lean_unbox(v_t_21_);
v_res_25_ = l_Lean_Widget_DiffTag_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_boxed_24_, v_h_22_, v_k_23_);
lean_dec(v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg(lean_object* v_wasChanged_26_){
_start:
{
lean_inc(v_wasChanged_26_);
return v_wasChanged_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(lean_object* v_wasChanged_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_27_);
lean_dec(v_wasChanged_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim(lean_object* v_motive_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_wasChanged_32_){
_start:
{
lean_inc(v_wasChanged_32_);
return v_wasChanged_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___boxed(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_wasChanged_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Widget_DiffTag_wasChanged_elim(v_motive_33_, v_t_boxed_37_, v_h_35_, v_wasChanged_36_);
lean_dec(v_wasChanged_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg(lean_object* v_willChange_39_){
_start:
{
lean_inc(v_willChange_39_);
return v_willChange_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(lean_object* v_willChange_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_40_);
lean_dec(v_willChange_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_willChange_45_){
_start:
{
lean_inc(v_willChange_45_);
return v_willChange_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_willChange_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Widget_DiffTag_willChange_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_willChange_49_);
lean_dec(v_willChange_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(lean_object* v_wasDeleted_52_){
_start:
{
lean_inc(v_wasDeleted_52_);
return v_wasDeleted_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(lean_object* v_wasDeleted_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(v_wasDeleted_53_);
lean_dec(v_wasDeleted_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_wasDeleted_58_){
_start:
{
lean_inc(v_wasDeleted_58_);
return v_wasDeleted_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_wasDeleted_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lean_Widget_DiffTag_wasDeleted_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_wasDeleted_62_);
lean_dec(v_wasDeleted_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg(lean_object* v_willDelete_65_){
_start:
{
lean_inc(v_willDelete_65_);
return v_willDelete_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(lean_object* v_willDelete_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_66_);
lean_dec(v_willDelete_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_willDelete_71_){
_start:
{
lean_inc(v_willDelete_71_);
return v_willDelete_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_willDelete_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Widget_DiffTag_willDelete_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_willDelete_75_);
lean_dec(v_willDelete_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg(lean_object* v_wasInserted_78_){
_start:
{
lean_inc(v_wasInserted_78_);
return v_wasInserted_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(lean_object* v_wasInserted_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_79_);
lean_dec(v_wasInserted_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_wasInserted_84_){
_start:
{
lean_inc(v_wasInserted_84_);
return v_wasInserted_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_wasInserted_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Lean_Widget_DiffTag_wasInserted_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_wasInserted_88_);
lean_dec(v_wasInserted_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg(lean_object* v_willInsert_91_){
_start:
{
lean_inc(v_willInsert_91_);
return v_willInsert_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(lean_object* v_willInsert_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_92_);
lean_dec(v_willInsert_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_willInsert_97_){
_start:
{
lean_inc(v_willInsert_97_);
return v_willInsert_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_willInsert_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Lean_Widget_DiffTag_willInsert_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_willInsert_101_);
lean_dec(v_willInsert_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson(uint8_t v_x_122_){
_start:
{
switch(v_x_122_)
{
case 0:
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1));
return v___x_123_;
}
case 1:
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3));
return v___x_124_;
}
case 2:
{
lean_object* v___x_125_; 
v___x_125_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5));
return v___x_125_;
}
case 3:
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7));
return v___x_126_;
}
case 4:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9));
return v___x_127_;
}
default: 
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11));
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___boxed(lean_object* v_x_129_){
_start:
{
uint8_t v_x_130__boxed_130_; lean_object* v_res_131_; 
v_x_130__boxed_130_ = lean_unbox(v_x_129_);
v_res_131_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_130__boxed_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson(lean_object* v_json_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Json_getTag_x3f(v_json_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1));
return v___x_160_;
}
else
{
lean_object* v_val_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_val_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v___x_159_, 1);
v___x_162_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10));
v___x_163_ = lean_string_dec_eq(v_val_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0));
v___x_165_ = lean_string_dec_eq(v_val_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2));
v___x_167_ = lean_string_dec_eq(v_val_161_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4));
v___x_169_ = lean_string_dec_eq(v_val_161_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6));
v___x_171_ = lean_string_dec_eq(v_val_161_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8));
v___x_173_ = lean_string_dec_eq(v_val_161_, v___x_172_);
lean_dec(v_val_161_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3));
return v___x_174_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4));
return v___x_175_;
}
}
else
{
lean_object* v___x_176_; 
lean_dec(v_val_161_);
v___x_176_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5));
return v___x_176_;
}
}
else
{
lean_object* v___x_177_; 
lean_dec(v_val_161_);
v___x_177_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6));
return v___x_177_;
}
}
else
{
lean_object* v___x_178_; 
lean_dec(v_val_161_);
v___x_178_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7));
return v___x_178_;
}
}
else
{
lean_object* v___x_179_; 
lean_dec(v_val_161_);
v___x_179_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8));
return v___x_179_;
}
}
else
{
lean_object* v___x_180_; 
lean_dec(v_val_161_);
v___x_180_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9));
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(lean_object* v_j_183_, lean_object* v_k_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = l_Lean_Json_getObjValD(v_j_183_, v_k_184_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(lean_object* v_j_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_j_187_, v_k_188_);
lean_dec_ref(v_k_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0));
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_x_192_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(lean_object* v_j_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = l_Lean_Json_getObjValD(v_j_196_, v_k_197_);
v___x_199_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(lean_object* v_j_200_, lean_object* v_k_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_j_200_, v_k_201_);
lean_dec_ref(v_k_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(lean_object* v_json_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v___x_207_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc_n(v_json_206_, 2);
v___x_208_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_206_, v___x_207_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_211_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_206_, v___x_210_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_214_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_json_206_, v___x_213_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_219_, 0, v_a_209_);
lean_ctor_set(v___x_219_, 1, v_a_212_);
lean_ctor_set(v___x_219_, 2, v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(lean_object* v_k_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec_ref(v_k_226_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_val_229_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_val_229_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_k_226_);
lean_ctor_set(v___x_230_, 1, v_val_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0___boxed(lean_object* v_k_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v_k_233_, v_x_234_);
lean_dec(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
if (lean_obj_tag(v_a_236_) == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_array_to_list(v_a_237_);
return v___x_238_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v___x_241_; 
v_head_239_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_head_239_);
v_tail_240_ = lean_ctor_get(v_a_236_, 1);
lean_inc(v_tail_240_);
lean_dec_ref_known(v_a_236_, 2);
v___x_241_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_237_, v_head_239_);
v_a_236_ = v_tail_240_;
v_a_237_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(lean_object* v_x_245_){
_start:
{
lean_object* v_info_246_; lean_object* v_subexprPos_247_; lean_object* v_diffStatus_x3f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_info_246_ = lean_ctor_get(v_x_245_, 0);
v_subexprPos_247_ = lean_ctor_get(v_x_245_, 1);
v_diffStatus_x3f_248_ = lean_ctor_get(v_x_245_, 2);
v___x_249_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_info_246_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_info_246_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_subexprPos_247_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_subexprPos_247_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_251_);
v___x_256_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_257_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v___x_256_, v_diffStatus_x3f_248_);
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_251_);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_255_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_252_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_));
v___x_262_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(v___x_260_, v___x_261_);
v___x_263_ = l_Lean_Json_mkObj(v___x_262_);
lean_dec(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34____boxed(lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v_x_264_);
lean_dec_ref(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_info_270_; lean_object* v_subexprPos_271_; lean_object* v_diffStatus_x3f_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_306_; 
v_info_270_ = lean_ctor_get(v_a_268_, 0);
v_subexprPos_271_ = lean_ctor_get(v_a_268_, 1);
v_diffStatus_x3f_272_ = lean_ctor_get(v_a_268_, 2);
v_isSharedCheck_306_ = !lean_is_exclusive(v_a_268_);
if (v_isSharedCheck_306_ == 0)
{
v___x_274_ = v_a_268_;
v_isShared_275_ = v_isSharedCheck_306_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_diffStatus_x3f_272_);
lean_inc(v_subexprPos_271_);
lean_inc(v_info_270_);
lean_dec(v_a_268_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_306_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_305_; 
v___x_276_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_277_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_276_, v_info_270_, v_a_269_);
lean_dec_ref(v_info_270_);
v_fst_278_ = lean_ctor_get(v___x_277_, 0);
v_snd_279_ = lean_ctor_get(v___x_277_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_305_ == 0)
{
v___x_281_ = v___x_277_;
v_isShared_282_ = v_isSharedCheck_305_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
lean_dec(v___x_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_305_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_fst_286_; 
v___x_283_ = l_Lean_SubExpr_Pos_toString(v_subexprPos_271_);
lean_dec(v_subexprPos_271_);
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
if (lean_obj_tag(v_diffStatus_x3f_272_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
v_fst_286_ = v___x_294_;
goto v___jp_285_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_304_; 
v_val_295_ = lean_ctor_get(v_diffStatus_x3f_272_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_diffStatus_x3f_272_);
if (v_isSharedCheck_304_ == 0)
{
v___x_297_ = v_diffStatus_x3f_272_;
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_val_295_);
lean_dec(v_diffStatus_x3f_272_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_299_ = lean_unbox(v_val_295_);
lean_dec(v_val_295_);
v___x_300_ = l_Lean_Widget_instToJsonDiffTag_toJson(v___x_299_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_300_);
v___x_302_ = v___x_297_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v_fst_286_ = v___x_302_;
goto v___jp_285_;
}
}
}
v___jp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 2, v_fst_286_);
lean_ctor_set(v___x_274_, 1, v___x_284_);
lean_ctor_set(v___x_274_, 0, v_fst_278_);
v___x_288_ = v___x_274_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_fst_278_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_fst_286_);
v___x_288_ = v_reuseFailAlloc_293_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v___x_288_);
lean_dec_ref(v___x_288_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_289_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_279_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(lean_object* v_x_307_){
_start:
{
lean_inc_ref(v_x_307_);
return v_x_307_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(v_x_308_);
lean_dec_ref(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_310_, lean_object* v_x_311_, lean_object* v___y_312_){
_start:
{
lean_inc_ref(v_x_311_);
return v_x_311_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(lean_object* v_00_u03b1_313_, lean_object* v_x_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(v_00_u03b1_313_, v_x_314_, v___y_315_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_x_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_j_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(v_j_317_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v_info_329_; lean_object* v_subexprPos_330_; lean_object* v_diffStatus_x3f_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_397_; 
v_a_328_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_319_, 1);
v_info_329_ = lean_ctor_get(v_a_328_, 0);
v_subexprPos_330_ = lean_ctor_get(v_a_328_, 1);
v_diffStatus_x3f_331_ = lean_ctor_get(v_a_328_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_397_ == 0)
{
v___x_333_ = v_a_328_;
v_isShared_334_ = v_isSharedCheck_397_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_diffStatus_x3f_331_);
lean_inc(v_subexprPos_330_);
lean_inc(v_info_329_);
lean_dec(v_a_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_397_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_336_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_335_, v_info_329_, v_a_318_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_del_object(v___x_333_);
lean_dec(v_diffStatus_x3f_331_);
lean_dec(v_subexprPos_330_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_336_, 1);
v___x_346_ = l_Lean_Json_getStr_x3f(v_subexprPos_330_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_345_);
lean_del_object(v___x_333_);
lean_dec(v_diffStatus_x3f_331_);
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
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_355_; lean_object* v___x_356_; 
v_a_355_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_346_, 1);
v___x_356_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_345_);
lean_del_object(v___x_333_);
lean_dec(v_diffStatus_x3f_331_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_396_; 
v_a_365_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_396_ == 0)
{
v___x_367_ = v___x_356_;
v_isShared_368_ = v_isSharedCheck_396_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_356_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_396_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_____do__lift_370_; 
if (lean_obj_tag(v_diffStatus_x3f_331_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
v_____do__lift_370_ = v___x_377_;
goto v___jp_369_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_395_; 
v_val_378_ = lean_ctor_get(v_diffStatus_x3f_331_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_diffStatus_x3f_331_);
if (v_isSharedCheck_395_ == 0)
{
v___x_380_ = v_diffStatus_x3f_331_;
v_isShared_381_ = v_isSharedCheck_395_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_val_378_);
lean_dec(v_diffStatus_x3f_331_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_395_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Widget_instFromJsonDiffTag_fromJson(v_val_378_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_380_);
lean_del_object(v___x_367_);
lean_dec(v_a_365_);
lean_dec(v_a_345_);
lean_del_object(v___x_333_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; 
v_a_391_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_382_, 1);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v_a_391_);
v___x_393_ = v___x_380_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v_____do__lift_370_ = v___x_393_;
goto v___jp_369_;
}
}
}
}
v___jp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 2, v_____do__lift_370_);
lean_ctor_set(v___x_333_, 1, v_a_365_);
lean_ctor_set(v___x_333_, 0, v_a_345_);
v___x_372_ = v___x_333_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_345_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_____do__lift_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_372_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(lean_object* v_j_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(v_j_398_, v_a_399_);
lean_dec_ref(v_a_399_);
return v_res_400_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object* v_x_407_, lean_object* v_y_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_lt(v_x_407_, v_y_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_eq(v_x_407_, v_y_408_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 2;
return v___x_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 1;
return v___x_412_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(lean_object* v_x_414_, lean_object* v_y_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_414_, v_y_415_);
lean_dec(v_y_415_);
lean_dec(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(lean_object* v___f_418_, lean_object* v_pm_419_, lean_object* v_inst_420_, lean_object* v_merger_421_, lean_object* v_info_422_){
_start:
{
lean_object* v_subexprPos_423_; lean_object* v___x_424_; 
v_subexprPos_423_ = lean_ctor_get(v_info_422_, 1);
lean_inc(v_subexprPos_423_);
v___x_424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_418_, v_pm_419_, v_subexprPos_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_toApplicative_425_; lean_object* v_toPure_426_; lean_object* v___x_427_; 
lean_dec(v_merger_421_);
v_toApplicative_425_ = lean_ctor_get(v_inst_420_, 0);
lean_inc_ref(v_toApplicative_425_);
lean_dec_ref(v_inst_420_);
v_toPure_426_ = lean_ctor_get(v_toApplicative_425_, 1);
lean_inc(v_toPure_426_);
lean_dec_ref(v_toApplicative_425_);
v___x_427_ = lean_apply_2(v_toPure_426_, lean_box(0), v_info_422_);
return v___x_427_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_429_; 
lean_dec_ref(v_inst_420_);
v_val_428_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_424_, 1);
v___x_429_ = lean_apply_2(v_merger_421_, v_info_422_, v_val_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object* v_inst_431_, lean_object* v_merger_432_, lean_object* v_pm_433_, lean_object* v_tt_434_){
_start:
{
if (lean_obj_tag(v_pm_433_) == 0)
{
lean_object* v___f_435_; lean_object* v___f_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0));
lean_inc_ref(v_inst_431_);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1), 5, 4);
lean_closure_set(v___f_436_, 0, v___f_435_);
lean_closure_set(v___f_436_, 1, v_pm_433_);
lean_closure_set(v___f_436_, 2, v_inst_431_);
lean_closure_set(v___f_436_, 3, v_merger_432_);
v___x_437_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_431_, v___f_436_, v_tt_434_);
return v___x_437_;
}
else
{
lean_object* v_toApplicative_438_; lean_object* v_toPure_439_; lean_object* v___x_440_; 
lean_dec(v_merger_432_);
v_toApplicative_438_ = lean_ctor_get(v_inst_431_, 0);
lean_inc_ref(v_toApplicative_438_);
lean_dec_ref(v_inst_431_);
v_toPure_439_ = lean_ctor_get(v_toApplicative_438_, 1);
lean_inc(v_toPure_439_);
lean_dec_ref(v_toApplicative_438_);
v___x_440_ = lean_apply_2(v_toPure_439_, lean_box(0), v_tt_434_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object* v_m_441_, lean_object* v_00_u03b1_442_, lean_object* v_inst_443_, lean_object* v_merger_444_, lean_object* v_pm_445_, lean_object* v_tt_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(v_inst_443_, v_merger_444_, v_pm_445_, v_tt_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object* v_tt_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t v_tag_450_, lean_object* v_c_451_){
_start:
{
lean_object* v_info_452_; lean_object* v_subexprPos_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v_info_452_ = lean_ctor_get(v_c_451_, 0);
v_subexprPos_453_ = lean_ctor_get(v_c_451_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_c_451_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v_c_451_, 2);
lean_dec(v_unused_463_);
v___x_455_ = v_c_451_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_subexprPos_453_);
lean_inc(v_info_452_);
lean_dec(v_c_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_box(v_tag_450_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_info_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_subexprPos_453_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object* v_tag_464_, lean_object* v_c_465_){
_start:
{
uint8_t v_tag_boxed_466_; lean_object* v_res_467_; 
v_tag_boxed_466_ = lean_unbox(v_tag_464_);
v_res_467_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_boxed_466_, v_c_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(lean_object* v_t_468_, lean_object* v_k_469_){
_start:
{
if (lean_obj_tag(v_t_468_) == 0)
{
lean_object* v_k_470_; lean_object* v_v_471_; lean_object* v_l_472_; lean_object* v_r_473_; uint8_t v___x_474_; 
v_k_470_ = lean_ctor_get(v_t_468_, 1);
v_v_471_ = lean_ctor_get(v_t_468_, 2);
v_l_472_ = lean_ctor_get(v_t_468_, 3);
v_r_473_ = lean_ctor_get(v_t_468_, 4);
v___x_474_ = lean_nat_dec_lt(v_k_469_, v_k_470_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_eq(v_k_469_, v_k_470_);
if (v___x_475_ == 0)
{
v_t_468_ = v_r_473_;
goto _start;
}
else
{
lean_object* v___x_477_; 
lean_inc(v_v_471_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_v_471_);
return v___x_477_;
}
}
else
{
v_t_468_ = v_l_472_;
goto _start;
}
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_box(0);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(lean_object* v_t_480_, lean_object* v_k_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_480_, v_k_481_);
lean_dec(v_k_481_);
lean_dec(v_t_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(lean_object* v_f_483_, size_t v_sz_484_, size_t v_i_485_, lean_object* v_bs_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_f_483_);
return v_bs_486_;
}
else
{
lean_object* v_v_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_bs_x27_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_v_489_ = lean_array_uget_borrowed(v_bs_486_, v_i_485_);
lean_inc(v_v_489_);
lean_inc_ref(v_f_483_);
v___x_490_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_483_, v_v_489_);
v___x_491_ = lean_unsigned_to_nat(0u);
v_bs_x27_492_ = lean_array_uset(v_bs_486_, v_i_485_, v___x_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_485_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_492_, v_i_485_, v___x_490_);
v_i_485_ = v___x_494_;
v_bs_486_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(lean_object* v_f_497_, lean_object* v_x_498_){
_start:
{
switch(lean_obj_tag(v_x_498_))
{
case 0:
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_f_497_);
v_a_500_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v_x_498_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v_x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
case 1:
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_a_508_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_x_498_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v_x_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v_sz_512_ = lean_array_size(v_a_508_);
v___x_513_ = ((size_t)0ULL);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_497_, v_sz_512_, v___x_513_, v_a_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
default: 
{
lean_object* v_a_519_; lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_a_519_);
v_a_520_ = lean_ctor_get(v_x_498_, 1);
lean_inc_ref(v_a_520_);
lean_dec_ref_known(v_x_498_, 2);
v___x_521_ = lean_apply_3(v_f_497_, v_a_519_, v_a_520_, lean_box(0));
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg___boxed(lean_object* v_f_522_, lean_object* v_x_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_522_, v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(lean_object* v_f_526_, lean_object* v_sz_527_, lean_object* v_i_528_, lean_object* v_bs_529_, lean_object* v___y_530_){
_start:
{
size_t v_sz_boxed_531_; size_t v_i_boxed_532_; lean_object* v_res_533_; 
v_sz_boxed_531_ = lean_unbox_usize(v_sz_527_);
lean_dec(v_sz_527_);
v_i_boxed_532_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_526_, v_sz_boxed_531_, v_i_boxed_532_, v_bs_529_);
return v_res_533_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(lean_object* v_infos_535_, lean_object* v_ctx_536_, lean_object* v_x_537_, lean_object* v_subTt_538_){
_start:
{
lean_object* v_fst_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_556_; 
v_fst_540_ = lean_ctor_get(v_x_537_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_x_537_, 1);
lean_dec(v_unused_557_);
v___x_542_ = v_x_537_;
v_isShared_543_ = v_isSharedCheck_556_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_fst_540_);
lean_dec(v_x_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_556_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_infos_535_, v_fst_540_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
lean_del_object(v___x_542_);
lean_dec(v_fst_540_);
v___x_545_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_536_, v_infos_535_, v_subTt_538_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_544_, 1);
v___x_547_ = lean_obj_once(&l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0, &l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0);
lean_inc_ref(v_ctx_536_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v_ctx_536_);
lean_ctor_set(v___x_548_, 1, v_val_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_548_);
v___x_550_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_536_, v_infos_535_, v_subTt_538_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___x_549_);
lean_ctor_set(v___x_552_, 1, v_fst_540_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 2);
lean_ctor_set(v___x_542_, 1, v___x_550_);
lean_ctor_set(v___x_542_, 0, v___x_552_);
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_550_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed(lean_object* v_infos_558_, lean_object* v_ctx_559_, lean_object* v_x_560_, lean_object* v_subTt_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(v_infos_558_, v_ctx_559_, v_x_560_, v_subTt_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(lean_object* v_ctx_564_, lean_object* v_infos_565_, lean_object* v_tt_566_){
_start:
{
lean_object* v___f_568_; lean_object* v___x_569_; 
v___f_568_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed), 5, 2);
lean_closure_set(v___f_568_, 0, v_infos_565_);
lean_closure_set(v___f_568_, 1, v_ctx_564_);
v___x_569_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v___f_568_, v_tt_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(lean_object* v_ctx_570_, lean_object* v_infos_571_, lean_object* v_tt_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_570_, v_infos_571_, v_tt_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(lean_object* v_00_u03b4_575_, lean_object* v_t_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_576_, v_k_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(lean_object* v_00_u03b4_579_, lean_object* v_t_580_, lean_object* v_k_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(v_00_u03b4_579_, v_t_580_, v_k_581_);
lean_dec(v_k_581_);
lean_dec(v_t_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_f_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_585_, v_x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_f_591_, lean_object* v_x_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(v_00_u03b1_589_, v_00_u03b2_590_, v_f_591_, v_x_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v_f_597_, size_t v_sz_598_, size_t v_i_599_, lean_object* v_bs_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_597_, v_sz_598_, v_i_599_, v_bs_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_f_605_, lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_bs_608_, lean_object* v___y_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_611_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(v_00_u03b1_603_, v_00_u03b2_604_, v_f_605_, v_sz_boxed_610_, v_i_boxed_611_, v_bs_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos(lean_object* v_ctx_613_, lean_object* v_infos_614_, lean_object* v_tt_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_613_, v_infos_614_, v_tt_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos___boxed(lean_object* v_ctx_618_, lean_object* v_infos_619_, lean_object* v_tt_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Widget_tagCodeInfos(v_ctx_618_, v_infos_619_, v_tt_620_);
return v_res_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(lean_object* v_opts_623_, lean_object* v_opt_624_){
_start:
{
lean_object* v_name_625_; lean_object* v_defValue_626_; lean_object* v_map_627_; lean_object* v___x_628_; 
v_name_625_ = lean_ctor_get(v_opt_624_, 0);
v_defValue_626_ = lean_ctor_get(v_opt_624_, 1);
v_map_627_ = lean_ctor_get(v_opts_623_, 0);
v___x_628_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_627_, v_name_625_);
if (lean_obj_tag(v___x_628_) == 0)
{
uint8_t v___x_629_; 
v___x_629_ = lean_unbox(v_defValue_626_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; 
v_val_630_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_628_, 1);
if (lean_obj_tag(v_val_630_) == 1)
{
uint8_t v_v_631_; 
v_v_631_ = lean_ctor_get_uint8(v_val_630_, 0);
lean_dec_ref_known(v_val_630_, 0);
return v_v_631_;
}
else
{
uint8_t v___x_632_; 
lean_dec(v_val_630_);
v___x_632_ = lean_unbox(v_defValue_626_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(lean_object* v_opts_633_, lean_object* v_opt_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_633_, v_opt_634_);
lean_dec_ref(v_opt_634_);
lean_dec_ref(v_opts_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(lean_object* v_e_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_hasMVar(v_e_637_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_e_637_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v_mctx_643_; lean_object* v___x_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; lean_object* v___x_647_; lean_object* v_cache_648_; lean_object* v_zetaDeltaFVarIds_649_; lean_object* v_postponed_650_; lean_object* v_diag_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_660_; 
v___x_642_ = lean_st_ref_get(v___y_638_);
v_mctx_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_mctx_643_);
lean_dec(v___x_642_);
v___x_644_ = l_Lean_instantiateMVarsCore(v_mctx_643_, v_e_637_);
v_fst_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_fst_645_);
v_snd_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_snd_646_);
lean_dec_ref(v___x_644_);
v___x_647_ = lean_st_ref_take(v___y_638_);
v_cache_648_ = lean_ctor_get(v___x_647_, 1);
v_zetaDeltaFVarIds_649_ = lean_ctor_get(v___x_647_, 2);
v_postponed_650_ = lean_ctor_get(v___x_647_, 3);
v_diag_651_ = lean_ctor_get(v___x_647_, 4);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_647_, 0);
lean_dec(v_unused_661_);
v___x_653_ = v___x_647_;
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_diag_651_);
lean_inc(v_postponed_650_);
lean_inc(v_zetaDeltaFVarIds_649_);
lean_inc(v_cache_648_);
lean_dec(v___x_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_snd_646_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_snd_646_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_cache_648_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_zetaDeltaFVarIds_649_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_postponed_650_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_diag_651_);
v___x_656_ = v_reuseFailAlloc_659_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_st_ref_set(v___y_638_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_fst_645_);
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(lean_object* v_e_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_662_, v___y_663_);
lean_dec(v___y_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(lean_object* v_e_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_666_, v___y_668_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(lean_object* v_e_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(v_e_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged(lean_object* v_e_682_, lean_object* v_delab_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_e_690_; lean_object* v_options_694_; lean_object* v_currNamespace_695_; lean_object* v_openDecls_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_options_694_ = lean_ctor_get(v_a_686_, 2);
v_currNamespace_695_ = lean_ctor_get(v_a_686_, 6);
v_openDecls_696_ = lean_ctor_get(v_a_686_, 7);
v___x_697_ = l_Lean_pp_raw;
v___x_698_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_options_694_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_box(1);
v___x_700_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_682_, v___x_699_, v_delab_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_725_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_725_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_725_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fmt_705_; lean_object* v_infos_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_env_710_; lean_object* v_mctx_711_; lean_object* v_ngen_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_fmt_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_fmt_705_);
v_infos_706_ = lean_ctor_get(v_a_701_, 1);
lean_inc(v_infos_706_);
lean_dec(v_a_701_);
v___x_707_ = lean_st_ref_get(v_a_687_);
v___x_708_ = lean_st_ref_get(v_a_685_);
v___x_709_ = lean_st_ref_get(v_a_687_);
v_env_710_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_707_);
v_mctx_711_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_mctx_711_);
lean_dec(v___x_708_);
v_ngen_712_ = lean_ctor_get(v___x_709_, 2);
lean_inc_ref(v_ngen_712_);
lean_dec(v___x_709_);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = l_Std_Format_defWidth;
v___x_715_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_705_, v___x_713_, v___x_714_);
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_696_);
lean_inc(v_currNamespace_695_);
lean_inc_ref(v_options_694_);
v___x_718_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_718_, 0, v_env_710_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
lean_ctor_set(v___x_718_, 3, v_mctx_711_);
lean_ctor_set(v___x_718_, 4, v_options_694_);
lean_ctor_set(v___x_718_, 5, v_currNamespace_695_);
lean_ctor_set(v___x_718_, 6, v_openDecls_696_);
lean_ctor_set(v___x_718_, 7, v_ngen_712_);
v___x_719_ = ((lean_object*)(l_Lean_Widget_ppExprTagged___closed__0));
v___x_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_716_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
v___x_721_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v___x_720_, v_infos_706_, v___x_715_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_721_);
v___x_723_ = v___x_703_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_700_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_700_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
uint8_t v___x_734_; 
lean_dec_ref(v_delab_683_);
v___x_734_ = l_Lean_getPPInstantiateMVars(v_options_694_);
if (v___x_734_ == 0)
{
v_e_690_ = v_e_682_;
goto v___jp_689_;
}
else
{
lean_object* v___x_735_; lean_object* v_a_736_; 
v___x_735_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_682_, v_a_685_);
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
v_e_690_ = v_a_736_;
goto v___jp_689_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_expr_dbg_to_string(v_e_690_);
lean_dec_ref(v_e_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged___boxed(lean_object* v_e_737_, lean_object* v_delab_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Widget_ppExprTagged(v_e_737_, v_delab_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_744_;
}
}
lean_object* runtime_initialize_Lean_Widget_TaggedText(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_InteractiveCode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Widget_TaggedText(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_InteractiveCode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Widget_TaggedText(uint8_t builtin);
lean_object* initialize_Lean_Widget_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_InteractiveCode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Widget_TaggedText(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_InteractiveCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_InteractiveCode(builtin);
}
#ifdef __cplusplus
}
#endif
