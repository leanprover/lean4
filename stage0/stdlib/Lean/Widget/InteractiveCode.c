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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_pp_raw;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_empty(lean_object*);
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx(uint8_t v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_4__boxed_14_; lean_object* v_res_15_; 
v_x_4__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lean_Widget_DiffTag_toCtorIdx(v_x_4__boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg(lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_17_);
lean_dec(v_k_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, uint8_t v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
uint8_t v_t_boxed_29_; lean_object* v_res_30_; 
v_t_boxed_29_ = lean_unbox(v_t_26_);
v_res_30_ = l_Lean_Widget_DiffTag_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_boxed_29_, v_h_27_, v_k_28_);
lean_dec(v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg(lean_object* v_wasChanged_31_){
_start:
{
lean_inc(v_wasChanged_31_);
return v_wasChanged_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(lean_object* v_wasChanged_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_32_);
lean_dec(v_wasChanged_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim(lean_object* v_motive_34_, uint8_t v_t_35_, lean_object* v_h_36_, lean_object* v_wasChanged_37_){
_start:
{
lean_inc(v_wasChanged_37_);
return v_wasChanged_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_wasChanged_41_){
_start:
{
uint8_t v_t_boxed_42_; lean_object* v_res_43_; 
v_t_boxed_42_ = lean_unbox(v_t_39_);
v_res_43_ = l_Lean_Widget_DiffTag_wasChanged_elim(v_motive_38_, v_t_boxed_42_, v_h_40_, v_wasChanged_41_);
lean_dec(v_wasChanged_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg(lean_object* v_willChange_44_){
_start:
{
lean_inc(v_willChange_44_);
return v_willChange_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(lean_object* v_willChange_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_45_);
lean_dec(v_willChange_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim(lean_object* v_motive_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_willChange_50_){
_start:
{
lean_inc(v_willChange_50_);
return v_willChange_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___boxed(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_willChange_54_){
_start:
{
uint8_t v_t_boxed_55_; lean_object* v_res_56_; 
v_t_boxed_55_ = lean_unbox(v_t_52_);
v_res_56_ = l_Lean_Widget_DiffTag_willChange_elim(v_motive_51_, v_t_boxed_55_, v_h_53_, v_willChange_54_);
lean_dec(v_willChange_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(lean_object* v_wasDeleted_57_){
_start:
{
lean_inc(v_wasDeleted_57_);
return v_wasDeleted_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(lean_object* v_wasDeleted_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(v_wasDeleted_58_);
lean_dec(v_wasDeleted_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim(lean_object* v_motive_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_wasDeleted_63_){
_start:
{
lean_inc(v_wasDeleted_63_);
return v_wasDeleted_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_wasDeleted_67_){
_start:
{
uint8_t v_t_boxed_68_; lean_object* v_res_69_; 
v_t_boxed_68_ = lean_unbox(v_t_65_);
v_res_69_ = l_Lean_Widget_DiffTag_wasDeleted_elim(v_motive_64_, v_t_boxed_68_, v_h_66_, v_wasDeleted_67_);
lean_dec(v_wasDeleted_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg(lean_object* v_willDelete_70_){
_start:
{
lean_inc(v_willDelete_70_);
return v_willDelete_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(lean_object* v_willDelete_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_71_);
lean_dec(v_willDelete_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim(lean_object* v_motive_73_, uint8_t v_t_74_, lean_object* v_h_75_, lean_object* v_willDelete_76_){
_start:
{
lean_inc(v_willDelete_76_);
return v_willDelete_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_willDelete_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lean_Widget_DiffTag_willDelete_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_willDelete_80_);
lean_dec(v_willDelete_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg(lean_object* v_wasInserted_83_){
_start:
{
lean_inc(v_wasInserted_83_);
return v_wasInserted_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(lean_object* v_wasInserted_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_84_);
lean_dec(v_wasInserted_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_wasInserted_89_){
_start:
{
lean_inc(v_wasInserted_89_);
return v_wasInserted_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___boxed(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_wasInserted_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lean_Widget_DiffTag_wasInserted_elim(v_motive_90_, v_t_boxed_94_, v_h_92_, v_wasInserted_93_);
lean_dec(v_wasInserted_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg(lean_object* v_willInsert_96_){
_start:
{
lean_inc(v_willInsert_96_);
return v_willInsert_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(lean_object* v_willInsert_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_97_);
lean_dec(v_willInsert_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_willInsert_102_){
_start:
{
lean_inc(v_willInsert_102_);
return v_willInsert_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_willInsert_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lean_Widget_DiffTag_willInsert_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_willInsert_106_);
lean_dec(v_willInsert_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson(uint8_t v_x_127_){
_start:
{
switch(v_x_127_)
{
case 0:
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1));
return v___x_128_;
}
case 1:
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3));
return v___x_129_;
}
case 2:
{
lean_object* v___x_130_; 
v___x_130_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5));
return v___x_130_;
}
case 3:
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7));
return v___x_131_;
}
case 4:
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9));
return v___x_132_;
}
default: 
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11));
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___boxed(lean_object* v_x_134_){
_start:
{
uint8_t v_x_130__boxed_135_; lean_object* v_res_136_; 
v_x_130__boxed_135_ = lean_unbox(v_x_134_);
v_res_136_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_130__boxed_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson(lean_object* v_json_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Json_getTag_x3f(v_json_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1));
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_val_166_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v___x_164_);
v___x_167_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10));
v___x_168_ = lean_string_dec_eq(v_val_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0));
v___x_170_ = lean_string_dec_eq(v_val_166_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2));
v___x_172_ = lean_string_dec_eq(v_val_166_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4));
v___x_174_ = lean_string_dec_eq(v_val_166_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6));
v___x_176_ = lean_string_dec_eq(v_val_166_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8));
v___x_178_ = lean_string_dec_eq(v_val_166_, v___x_177_);
lean_dec(v_val_166_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3));
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4));
return v___x_180_;
}
}
else
{
lean_object* v___x_181_; 
lean_dec(v_val_166_);
v___x_181_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5));
return v___x_181_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_val_166_);
v___x_182_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6));
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_val_166_);
v___x_183_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7));
return v___x_183_;
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v_val_166_);
v___x_184_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8));
return v___x_184_;
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v_val_166_);
v___x_185_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9));
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(lean_object* v_j_188_, lean_object* v_k_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Lean_Json_getObjValD(v_j_188_, v_k_189_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(lean_object* v_j_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_j_192_, v_k_193_);
lean_dec_ref(v_k_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0));
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_x_197_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(lean_object* v_j_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = l_Lean_Json_getObjValD(v_j_201_, v_k_202_);
v___x_204_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(lean_object* v_j_205_, lean_object* v_k_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_j_205_, v_k_206_);
lean_dec_ref(v_k_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(lean_object* v_json_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_a_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v___x_212_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_json_211_);
v___x_213_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_211_, v___x_212_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_json_211_);
v___x_216_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_211_, v___x_215_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref(v___x_216_);
v___x_218_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_219_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_json_211_, v___x_218_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v_a_214_);
lean_ctor_set(v___x_224_, 1, v_a_217_);
lean_ctor_set(v___x_224_, 2, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(lean_object* v_k_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_233_; 
lean_dec_ref(v_k_231_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_val_234_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_val_234_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_k_231_);
lean_ctor_set(v___x_235_, 1, v_val_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0___boxed(lean_object* v_k_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v_k_238_, v_x_239_);
lean_dec(v_x_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_array_to_list(v_a_242_);
return v___x_243_;
}
else
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v___x_246_; 
v_head_244_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_head_244_);
v_tail_245_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_tail_245_);
lean_dec_ref(v_a_241_);
v___x_246_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_242_, v_head_244_);
v_a_241_ = v_tail_245_;
v_a_242_ = v___x_246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(lean_object* v_x_250_){
_start:
{
lean_object* v_info_251_; lean_object* v_subexprPos_252_; lean_object* v_diffStatus_x3f_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_info_251_ = lean_ctor_get(v_x_250_, 0);
v_subexprPos_252_ = lean_ctor_get(v_x_250_, 1);
v_diffStatus_x3f_253_ = lean_ctor_get(v_x_250_, 2);
v___x_254_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_info_251_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_info_251_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_subexprPos_252_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_subexprPos_252_);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
v___x_261_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_262_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v___x_261_, v_diffStatus_x3f_253_);
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_256_);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_257_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_));
v___x_267_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(v___x_265_, v___x_266_);
v___x_268_ = l_Lean_Json_mkObj(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed(lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v_x_269_);
lean_dec_ref(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_info_275_; lean_object* v_subexprPos_276_; lean_object* v_diffStatus_x3f_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_311_; 
v_info_275_ = lean_ctor_get(v_a_273_, 0);
v_subexprPos_276_ = lean_ctor_get(v_a_273_, 1);
v_diffStatus_x3f_277_ = lean_ctor_get(v_a_273_, 2);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_273_);
if (v_isSharedCheck_311_ == 0)
{
v___x_279_ = v_a_273_;
v_isShared_280_ = v_isSharedCheck_311_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_diffStatus_x3f_277_);
lean_inc(v_subexprPos_276_);
lean_inc(v_info_275_);
lean_dec(v_a_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_311_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_310_; 
v___x_281_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_282_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_281_, v_info_275_, v_a_274_);
lean_dec_ref(v_info_275_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
v_snd_284_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_310_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_310_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snd_284_);
lean_inc(v_fst_283_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_310_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_fst_291_; 
v___x_288_ = l_Lean_SubExpr_Pos_toString(v_subexprPos_276_);
lean_dec(v_subexprPos_276_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
if (lean_obj_tag(v_diffStatus_x3f_277_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
v_fst_291_ = v___x_299_;
goto v___jp_290_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_309_; 
v_val_300_ = lean_ctor_get(v_diffStatus_x3f_277_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_diffStatus_x3f_277_);
if (v_isSharedCheck_309_ == 0)
{
v___x_302_ = v_diffStatus_x3f_277_;
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_dec(v_diffStatus_x3f_277_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_unbox(v_val_300_);
lean_dec(v_val_300_);
v___x_305_ = l_Lean_Widget_instToJsonDiffTag_toJson(v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
v_fst_291_ = v___x_307_;
goto v___jp_290_;
}
}
}
v___jp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 2, v_fst_291_);
lean_ctor_set(v___x_279_, 1, v___x_289_);
lean_ctor_set(v___x_279_, 0, v_fst_283_);
v___x_293_ = v___x_279_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_fst_283_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_fst_291_);
v___x_293_ = v_reuseFailAlloc_298_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v___x_293_);
lean_dec_ref(v___x_293_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_294_);
v___x_296_ = v___x_286_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_snd_284_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(lean_object* v_x_312_){
_start:
{
lean_inc_ref(v_x_312_);
return v_x_312_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(lean_object* v_x_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(v_x_313_);
lean_dec_ref(v_x_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_315_, lean_object* v_x_316_, lean_object* v___y_317_){
_start:
{
lean_inc_ref(v_x_316_);
return v_x_316_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(lean_object* v_00_u03b1_318_, lean_object* v_x_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(v_00_u03b1_318_, v_x_319_, v___y_320_);
lean_dec_ref(v___y_320_);
lean_dec_ref(v_x_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_j_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(v_j_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_a_323_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v_info_334_; lean_object* v_subexprPos_335_; lean_object* v_diffStatus_x3f_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_402_; 
v_a_333_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_324_);
v_info_334_ = lean_ctor_get(v_a_333_, 0);
v_subexprPos_335_ = lean_ctor_get(v_a_333_, 1);
v_diffStatus_x3f_336_ = lean_ctor_get(v_a_333_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_333_);
if (v_isSharedCheck_402_ == 0)
{
v___x_338_ = v_a_333_;
v_isShared_339_ = v_isSharedCheck_402_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_diffStatus_x3f_336_);
lean_inc(v_subexprPos_335_);
lean_inc(v_info_334_);
lean_dec(v_a_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_402_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_341_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_340_, v_info_334_, v_a_323_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_del_object(v___x_338_);
lean_dec(v_diffStatus_x3f_336_);
lean_dec(v_subexprPos_335_);
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_341_);
v___x_351_ = l_Lean_Json_getStr_x3f(v_subexprPos_335_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_350_);
lean_del_object(v___x_338_);
lean_dec(v_diffStatus_x3f_336_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_351_);
v___x_361_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_350_);
lean_del_object(v___x_338_);
lean_dec(v_diffStatus_x3f_336_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_401_; 
v_a_370_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_401_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_401_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_401_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_____do__lift_375_; 
if (lean_obj_tag(v_diffStatus_x3f_336_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
v_____do__lift_375_ = v___x_382_;
goto v___jp_374_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_400_; 
v_val_383_ = lean_ctor_get(v_diffStatus_x3f_336_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_diffStatus_x3f_336_);
if (v_isSharedCheck_400_ == 0)
{
v___x_385_ = v_diffStatus_x3f_336_;
v_isShared_386_ = v_isSharedCheck_400_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_val_383_);
lean_dec(v_diffStatus_x3f_336_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_400_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Widget_instFromJsonDiffTag_fromJson(v_val_383_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_del_object(v___x_385_);
lean_del_object(v___x_372_);
lean_dec(v_a_370_);
lean_dec(v_a_350_);
lean_del_object(v___x_338_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_396_);
lean_dec_ref(v___x_387_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_a_396_);
v___x_398_ = v___x_385_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
v_____do__lift_375_ = v___x_398_;
goto v___jp_374_;
}
}
}
}
v___jp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 2, v_____do__lift_375_);
lean_ctor_set(v___x_338_, 1, v_a_370_);
lean_ctor_set(v___x_338_, 0, v_a_350_);
v___x_377_ = v___x_338_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_350_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_a_370_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_____do__lift_375_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_377_);
v___x_379_ = v___x_372_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
LEAN_EXPORT uint8_t l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object* v_x_409_, lean_object* v_y_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_lt(v_x_409_, v_y_410_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_eq(v_x_409_, v_y_410_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 2;
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(lean_object* v_x_416_, lean_object* v_y_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_416_, v_y_417_);
lean_dec(v_y_417_);
lean_dec(v_x_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(lean_object* v___f_420_, lean_object* v_pm_421_, lean_object* v_inst_422_, lean_object* v_merger_423_, lean_object* v_info_424_){
_start:
{
lean_object* v_subexprPos_425_; lean_object* v___x_426_; 
v_subexprPos_425_ = lean_ctor_get(v_info_424_, 1);
lean_inc(v_subexprPos_425_);
v___x_426_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_420_, v_pm_421_, v_subexprPos_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_toApplicative_427_; lean_object* v_toPure_428_; lean_object* v___x_429_; 
lean_dec(v_merger_423_);
v_toApplicative_427_ = lean_ctor_get(v_inst_422_, 0);
lean_inc_ref(v_toApplicative_427_);
lean_dec_ref(v_inst_422_);
v_toPure_428_ = lean_ctor_get(v_toApplicative_427_, 1);
lean_inc(v_toPure_428_);
lean_dec_ref(v_toApplicative_427_);
v___x_429_ = lean_apply_2(v_toPure_428_, lean_box(0), v_info_424_);
return v___x_429_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_431_; 
lean_dec_ref(v_inst_422_);
v_val_430_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_430_);
lean_dec_ref(v___x_426_);
v___x_431_ = lean_apply_2(v_merger_423_, v_info_424_, v_val_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object* v_inst_433_, lean_object* v_merger_434_, lean_object* v_pm_435_, lean_object* v_tt_436_){
_start:
{
if (lean_obj_tag(v_pm_435_) == 0)
{
lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___x_439_; 
v___f_437_ = ((lean_object*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0));
lean_inc_ref(v_inst_433_);
v___f_438_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1), 5, 4);
lean_closure_set(v___f_438_, 0, v___f_437_);
lean_closure_set(v___f_438_, 1, v_pm_435_);
lean_closure_set(v___f_438_, 2, v_inst_433_);
lean_closure_set(v___f_438_, 3, v_merger_434_);
v___x_439_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_433_, v___f_438_, v_tt_436_);
return v___x_439_;
}
else
{
lean_object* v_toApplicative_440_; lean_object* v_toPure_441_; lean_object* v___x_442_; 
lean_dec(v_merger_434_);
v_toApplicative_440_ = lean_ctor_get(v_inst_433_, 0);
lean_inc_ref(v_toApplicative_440_);
lean_dec_ref(v_inst_433_);
v_toPure_441_ = lean_ctor_get(v_toApplicative_440_, 1);
lean_inc(v_toPure_441_);
lean_dec_ref(v_toApplicative_440_);
v___x_442_ = lean_apply_2(v_toPure_441_, lean_box(0), v_tt_436_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object* v_m_443_, lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_merger_446_, lean_object* v_pm_447_, lean_object* v_tt_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(v_inst_445_, v_merger_446_, v_pm_447_, v_tt_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object* v_tt_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t v_tag_452_, lean_object* v_c_453_){
_start:
{
lean_object* v_info_454_; lean_object* v_subexprPos_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v_info_454_ = lean_ctor_get(v_c_453_, 0);
v_subexprPos_455_ = lean_ctor_get(v_c_453_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_c_453_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_c_453_, 2);
lean_dec(v_unused_465_);
v___x_457_ = v_c_453_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_subexprPos_455_);
lean_inc(v_info_454_);
lean_dec(v_c_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_box(v_tag_452_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 2, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_info_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_subexprPos_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object* v_tag_466_, lean_object* v_c_467_){
_start:
{
uint8_t v_tag_boxed_468_; lean_object* v_res_469_; 
v_tag_boxed_468_ = lean_unbox(v_tag_466_);
v_res_469_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_boxed_468_, v_c_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(lean_object* v_t_470_, lean_object* v_k_471_){
_start:
{
if (lean_obj_tag(v_t_470_) == 0)
{
lean_object* v_k_472_; lean_object* v_v_473_; lean_object* v_l_474_; lean_object* v_r_475_; uint8_t v___x_476_; 
v_k_472_ = lean_ctor_get(v_t_470_, 1);
v_v_473_ = lean_ctor_get(v_t_470_, 2);
v_l_474_ = lean_ctor_get(v_t_470_, 3);
v_r_475_ = lean_ctor_get(v_t_470_, 4);
v___x_476_ = lean_nat_dec_lt(v_k_471_, v_k_472_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_eq(v_k_471_, v_k_472_);
if (v___x_477_ == 0)
{
v_t_470_ = v_r_475_;
goto _start;
}
else
{
lean_object* v___x_479_; 
lean_inc(v_v_473_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_v_473_);
return v___x_479_;
}
}
else
{
v_t_470_ = v_l_474_;
goto _start;
}
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_box(0);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(lean_object* v_t_482_, lean_object* v_k_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_482_, v_k_483_);
lean_dec(v_k_483_);
lean_dec(v_t_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(lean_object* v_f_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_490_ == 0)
{
lean_dec_ref(v_f_485_);
return v_bs_488_;
}
else
{
lean_object* v_v_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_v_491_ = lean_array_uget_borrowed(v_bs_488_, v_i_487_);
lean_inc(v_v_491_);
lean_inc_ref(v_f_485_);
v___x_492_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_485_, v_v_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_487_, v___x_495_);
v___x_497_ = lean_array_uset(v_bs_x27_494_, v_i_487_, v___x_492_);
v_i_487_ = v___x_496_;
v_bs_488_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(lean_object* v_f_499_, lean_object* v_x_500_){
_start:
{
switch(lean_obj_tag(v_x_500_))
{
case 0:
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_f_499_);
v_a_502_ = lean_ctor_get(v_x_500_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v_x_500_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v_x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
case 1:
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_520_; 
v_a_510_ = lean_ctor_get(v_x_500_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_512_ = v_x_500_;
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v_x_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v_sz_514_ = lean_array_size(v_a_510_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_499_, v_sz_514_, v___x_515_, v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
default: 
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_a_521_);
v_a_522_ = lean_ctor_get(v_x_500_, 1);
lean_inc_ref(v_a_522_);
lean_dec_ref(v_x_500_);
v___x_523_ = lean_apply_3(v_f_499_, v_a_521_, v_a_522_, lean_box(0));
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg___boxed(lean_object* v_f_524_, lean_object* v_x_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_524_, v_x_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(lean_object* v_f_528_, lean_object* v_sz_529_, lean_object* v_i_530_, lean_object* v_bs_531_, lean_object* v___y_532_){
_start:
{
size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_sz_boxed_533_ = lean_unbox_usize(v_sz_529_);
lean_dec(v_sz_529_);
v_i_boxed_534_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_528_, v_sz_boxed_533_, v_i_boxed_534_, v_bs_531_);
return v_res_535_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(lean_object* v_infos_537_, lean_object* v_ctx_538_, lean_object* v_x_539_, lean_object* v_subTt_540_){
_start:
{
lean_object* v_fst_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_558_; 
v_fst_542_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v_x_539_, 1);
lean_dec(v_unused_559_);
v___x_544_ = v_x_539_;
v_isShared_545_ = v_isSharedCheck_558_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_fst_542_);
lean_dec(v_x_539_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_558_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_infos_537_, v_fst_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
lean_del_object(v___x_544_);
lean_dec(v_fst_542_);
v___x_547_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_538_, v_infos_537_, v_subTt_540_);
return v___x_547_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v_val_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_548_);
lean_dec_ref(v___x_546_);
v___x_549_ = lean_obj_once(&l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0, &l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0);
lean_inc_ref(v_ctx_538_);
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v_ctx_538_);
lean_ctor_set(v___x_550_, 1, v_val_548_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
v___x_551_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_550_);
v___x_552_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_538_, v_infos_537_, v_subTt_540_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v_fst_542_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 2);
lean_ctor_set(v___x_544_, 1, v___x_552_);
lean_ctor_set(v___x_544_, 0, v___x_554_);
v___x_556_ = v___x_544_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_552_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed(lean_object* v_infos_560_, lean_object* v_ctx_561_, lean_object* v_x_562_, lean_object* v_subTt_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(v_infos_560_, v_ctx_561_, v_x_562_, v_subTt_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(lean_object* v_ctx_566_, lean_object* v_infos_567_, lean_object* v_tt_568_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; 
v___f_570_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed), 5, 2);
lean_closure_set(v___f_570_, 0, v_infos_567_);
lean_closure_set(v___f_570_, 1, v_ctx_566_);
v___x_571_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v___f_570_, v_tt_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(lean_object* v_ctx_572_, lean_object* v_infos_573_, lean_object* v_tt_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_572_, v_infos_573_, v_tt_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(lean_object* v_00_u03b4_577_, lean_object* v_t_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_578_, v_k_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(lean_object* v_00_u03b4_581_, lean_object* v_t_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(v_00_u03b4_581_, v_t_582_, v_k_583_);
lean_dec(v_k_583_);
lean_dec(v_t_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_f_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_587_, v_x_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(lean_object* v_00_u03b1_591_, lean_object* v_00_u03b2_592_, lean_object* v_f_593_, lean_object* v_x_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(v_00_u03b1_591_, v_00_u03b2_592_, v_f_593_, v_x_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_f_599_, size_t v_sz_600_, size_t v_i_601_, lean_object* v_bs_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_599_, v_sz_600_, v_i_601_, v_bs_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_f_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_bs_610_, lean_object* v___y_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_613_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(v_00_u03b1_605_, v_00_u03b2_606_, v_f_607_, v_sz_boxed_612_, v_i_boxed_613_, v_bs_610_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos(lean_object* v_ctx_615_, lean_object* v_infos_616_, lean_object* v_tt_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_615_, v_infos_616_, v_tt_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos___boxed(lean_object* v_ctx_620_, lean_object* v_infos_621_, lean_object* v_tt_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Widget_tagCodeInfos(v_ctx_620_, v_infos_621_, v_tt_622_);
return v_res_624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(lean_object* v_opts_625_, lean_object* v_opt_626_){
_start:
{
lean_object* v_name_627_; lean_object* v_defValue_628_; lean_object* v_map_629_; lean_object* v___x_630_; 
v_name_627_ = lean_ctor_get(v_opt_626_, 0);
v_defValue_628_ = lean_ctor_get(v_opt_626_, 1);
v_map_629_ = lean_ctor_get(v_opts_625_, 0);
v___x_630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_629_, v_name_627_);
if (lean_obj_tag(v___x_630_) == 0)
{
uint8_t v___x_631_; 
v___x_631_ = lean_unbox(v_defValue_628_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; 
v_val_632_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v___x_630_);
if (lean_obj_tag(v_val_632_) == 1)
{
uint8_t v_v_633_; 
v_v_633_ = lean_ctor_get_uint8(v_val_632_, 0);
lean_dec_ref(v_val_632_);
return v_v_633_;
}
else
{
uint8_t v___x_634_; 
lean_dec(v_val_632_);
v___x_634_ = lean_unbox(v_defValue_628_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(lean_object* v_opts_635_, lean_object* v_opt_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_635_, v_opt_636_);
lean_dec_ref(v_opt_636_);
lean_dec_ref(v_opts_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(lean_object* v_e_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = l_Lean_Expr_hasMVar(v_e_639_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_e_639_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v_mctx_645_; lean_object* v___x_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_649_; lean_object* v_cache_650_; lean_object* v_zetaDeltaFVarIds_651_; lean_object* v_postponed_652_; lean_object* v_diag_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v___x_644_ = lean_st_ref_get(v___y_640_);
v_mctx_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_mctx_645_);
lean_dec(v___x_644_);
v___x_646_ = l_Lean_instantiateMVarsCore(v_mctx_645_, v_e_639_);
v_fst_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_fst_647_);
v_snd_648_ = lean_ctor_get(v___x_646_, 1);
lean_inc(v_snd_648_);
lean_dec_ref(v___x_646_);
v___x_649_ = lean_st_ref_take(v___y_640_);
v_cache_650_ = lean_ctor_get(v___x_649_, 1);
v_zetaDeltaFVarIds_651_ = lean_ctor_get(v___x_649_, 2);
v_postponed_652_ = lean_ctor_get(v___x_649_, 3);
v_diag_653_ = lean_ctor_get(v___x_649_, 4);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_663_);
v___x_655_ = v___x_649_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_diag_653_);
lean_inc(v_postponed_652_);
lean_inc(v_zetaDeltaFVarIds_651_);
lean_inc(v_cache_650_);
lean_dec(v___x_649_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_snd_648_);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_snd_648_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_cache_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_zetaDeltaFVarIds_651_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_postponed_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_diag_653_);
v___x_658_ = v_reuseFailAlloc_661_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_st_ref_set(v___y_640_, v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_fst_647_);
return v___x_660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(lean_object* v_e_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_664_, v___y_665_);
lean_dec(v___y_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(lean_object* v_e_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_668_, v___y_670_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(lean_object* v_e_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(v_e_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged(lean_object* v_e_684_, lean_object* v_delab_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_e_692_; lean_object* v_options_696_; lean_object* v_currNamespace_697_; lean_object* v_openDecls_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_options_696_ = lean_ctor_get(v_a_688_, 2);
lean_inc_ref(v_options_696_);
v_currNamespace_697_ = lean_ctor_get(v_a_688_, 6);
lean_inc(v_currNamespace_697_);
v_openDecls_698_ = lean_ctor_get(v_a_688_, 7);
lean_inc(v_openDecls_698_);
v___x_699_ = l_Lean_pp_raw;
v___x_700_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_options_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_box(1);
lean_inc(v_a_689_);
lean_inc(v_a_687_);
v___x_702_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_684_, v___x_701_, v_delab_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_727_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_727_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_fmt_707_; lean_object* v_infos_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_env_712_; lean_object* v_mctx_713_; lean_object* v_ngen_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_fmt_707_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_fmt_707_);
v_infos_708_ = lean_ctor_get(v_a_703_, 1);
lean_inc(v_infos_708_);
lean_dec(v_a_703_);
v___x_709_ = lean_st_ref_get(v_a_689_);
v___x_710_ = lean_st_ref_get(v_a_687_);
lean_dec(v_a_687_);
v___x_711_ = lean_st_ref_get(v_a_689_);
lean_dec(v_a_689_);
v_env_712_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_709_);
v_mctx_713_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_mctx_713_);
lean_dec(v___x_710_);
v_ngen_714_ = lean_ctor_get(v___x_711_, 2);
lean_inc_ref(v_ngen_714_);
lean_dec(v___x_711_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_Std_Format_defWidth;
v___x_717_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_707_, v___x_715_, v___x_716_);
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_instInhabitedFileMap_default;
v___x_720_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_720_, 0, v_env_712_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
lean_ctor_set(v___x_720_, 3, v_mctx_713_);
lean_ctor_set(v___x_720_, 4, v_options_696_);
lean_ctor_set(v___x_720_, 5, v_currNamespace_697_);
lean_ctor_set(v___x_720_, 6, v_openDecls_698_);
lean_ctor_set(v___x_720_, 7, v_ngen_714_);
v___x_721_ = ((lean_object*)(l_Lean_Widget_ppExprTagged___closed__0));
v___x_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_718_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
v___x_723_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v___x_722_, v_infos_708_, v___x_717_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_723_);
v___x_725_ = v___x_705_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_openDecls_698_);
lean_dec(v_currNamespace_697_);
lean_dec_ref(v_options_696_);
lean_dec(v_a_689_);
lean_dec(v_a_687_);
v_a_728_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_702_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_702_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
uint8_t v___x_736_; 
lean_dec(v_openDecls_698_);
lean_dec(v_currNamespace_697_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec_ref(v_a_686_);
lean_dec_ref(v_delab_685_);
v___x_736_ = l_Lean_getPPInstantiateMVars(v_options_696_);
lean_dec_ref(v_options_696_);
if (v___x_736_ == 0)
{
lean_dec(v_a_687_);
v_e_692_ = v_e_684_;
goto v___jp_691_;
}
else
{
lean_object* v___x_737_; lean_object* v_a_738_; 
v___x_737_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_684_, v_a_687_);
lean_dec(v_a_687_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v___x_737_);
v_e_692_ = v_a_738_;
goto v___jp_691_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_expr_dbg_to_string(v_e_692_);
lean_dec_ref(v_e_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged___boxed(lean_object* v_e_739_, lean_object* v_delab_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Widget_ppExprTagged(v_e_739_, v_delab_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
return v_res_746_;
}
}
lean_object* runtime_initialize_Lean_Widget_TaggedText(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_InteractiveCode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
