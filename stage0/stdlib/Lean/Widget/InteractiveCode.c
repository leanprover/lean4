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
lean_object* l_Lean_PersistentArray_empty___redArg();
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_pp_raw;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Widget_DiffTag_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Widget_DiffTag_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Widget_DiffTag_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Widget_DiffTag_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Widget_DiffTag_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg(lean_object* v_wasChanged_24_){
_start:
{
lean_inc(v_wasChanged_24_);
return v_wasChanged_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(lean_object* v_wasChanged_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_25_);
lean_dec(v_wasChanged_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Widget_DiffTag_wasChanged_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_wasChanged_30_){
_start:
{
lean_inc(v_wasChanged_30_);
return v_wasChanged_30_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_wasChanged_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_wasChanged_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Widget_DiffTag_wasChanged_elim(lean_box(0), v_t_28_, lean_box(0), v_wasChanged_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_wasChanged_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Widget_DiffTag_wasChanged_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_wasChanged_35_);
lean_dec(v_wasChanged_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg(lean_object* v_willChange_38_){
_start:
{
lean_inc(v_willChange_38_);
return v_willChange_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(lean_object* v_willChange_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_39_);
lean_dec(v_willChange_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Widget_DiffTag_willChange_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_willChange_44_){
_start:
{
lean_inc(v_willChange_44_);
return v_willChange_44_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_willChange_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_willChange_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Widget_DiffTag_willChange_elim(lean_box(0), v_t_42_, lean_box(0), v_willChange_44_);
stack->m_obj
 = v_res_45_;
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
lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_wasDeleted_58_){
_start:
{
lean_inc(v_wasDeleted_58_);
return v_wasDeleted_58_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_wasDeleted_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_wasDeleted_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Widget_DiffTag_wasDeleted_elim(lean_box(0), v_t_56_, lean_box(0), v_wasDeleted_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_wasDeleted_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Widget_DiffTag_wasDeleted_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_wasDeleted_63_);
lean_dec(v_wasDeleted_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg(lean_object* v_willDelete_66_){
_start:
{
lean_inc(v_willDelete_66_);
return v_willDelete_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(lean_object* v_willDelete_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_67_);
lean_dec(v_willDelete_67_);
return v_res_68_;
}
}
lean_object* l_Lean_Widget_DiffTag_willDelete_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_willDelete_72_){
_start:
{
lean_inc(v_willDelete_72_);
return v_willDelete_72_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_willDelete_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_willDelete_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Widget_DiffTag_willDelete_elim(lean_box(0), v_t_70_, lean_box(0), v_willDelete_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_willDelete_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Lean_Widget_DiffTag_willDelete_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_willDelete_77_);
lean_dec(v_willDelete_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg(lean_object* v_wasInserted_80_){
_start:
{
lean_inc(v_wasInserted_80_);
return v_wasInserted_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(lean_object* v_wasInserted_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_81_);
lean_dec(v_wasInserted_81_);
return v_res_82_;
}
}
lean_object* l_Lean_Widget_DiffTag_wasInserted_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_wasInserted_86_){
_start:
{
lean_inc(v_wasInserted_86_);
return v_wasInserted_86_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_wasInserted_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_wasInserted_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Widget_DiffTag_wasInserted_elim(lean_box(0), v_t_84_, lean_box(0), v_wasInserted_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_wasInserted_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Lean_Widget_DiffTag_wasInserted_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_wasInserted_91_);
lean_dec(v_wasInserted_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg(lean_object* v_willInsert_94_){
_start:
{
lean_inc(v_willInsert_94_);
return v_willInsert_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(lean_object* v_willInsert_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_95_);
lean_dec(v_willInsert_95_);
return v_res_96_;
}
}
lean_object* l_Lean_Widget_DiffTag_willInsert_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_willInsert_100_){
_start:
{
lean_inc(v_willInsert_100_);
return v_willInsert_100_;
}
}
LEAN_EXPORT void l_Lean_Widget_DiffTag_willInsert_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_98_ = stack[1].m_num;
lean_object* v_willInsert_100_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_Widget_DiffTag_willInsert_elim(lean_box(0), v_t_98_, lean_box(0), v_willInsert_100_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_willInsert_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Lean_Widget_DiffTag_willInsert_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_willInsert_105_);
lean_dec(v_willInsert_105_);
return v_res_107_;
}
}
lean_object* l_Lean_Widget_instToJsonDiffTag_toJson(uint8_t v_x_126_){
_start:
{
switch(v_x_126_)
{
case 0:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1));
return v___x_127_;
}
case 1:
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3));
return v___x_128_;
}
case 2:
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5));
return v___x_129_;
}
case 3:
{
lean_object* v___x_130_; 
v___x_130_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7));
return v___x_130_;
}
case 4:
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9));
return v___x_131_;
}
default: 
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11));
return v___x_132_;
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_instToJsonDiffTag_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_126_ = stack[0].m_num;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_126_);
stack->m_obj
 = v_res_133_;
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
lean_dec_ref_known(v___x_164_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0));
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
v___x_204_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_203_);
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
lean_inc_n(v_json_211_, 2);
v___x_213_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_211_, v___x_212_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(lean_object* v_k_231_, lean_object* v_x_232_){
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0___boxed(lean_object* v_k_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v_k_238_, v_x_239_);
lean_dec(v_x_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(lean_object* v_a_241_, lean_object* v_a_242_){
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
lean_dec_ref_known(v_a_241_, 2);
v___x_246_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_242_, v_head_244_);
v_a_241_ = v_tail_245_;
v_a_242_ = v___x_246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(lean_object* v_x_250_){
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
v___x_262_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v___x_261_, v_diffStatus_x3f_253_);
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_256_);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_257_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_));
v___x_267_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(v___x_265_, v___x_266_);
v___x_268_ = l_Lean_Json_mkObj(v___x_267_);
lean_dec(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34____boxed(lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v_x_269_);
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
v___x_294_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v___x_293_);
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
lean_dec_ref_known(v___x_324_, 1);
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
lean_dec_ref_known(v___x_341_, 1);
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
lean_dec_ref_known(v___x_351_, 1);
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
lean_dec_ref_known(v___x_387_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(lean_object* v_j_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(v_j_403_, v_a_404_);
lean_dec_ref(v_a_404_);
return v_res_405_;
}
}
uint8_t l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object* v_x_412_, lean_object* v_y_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_lt(v_x_412_, v_y_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_eq(v_x_412_, v_y_413_);
if (v___x_415_ == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 2;
return v___x_416_;
}
else
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_412_ = stack[0].m_obj;
lean_object* v_y_413_ = stack[1].m_obj;
uint8_t v_res_419_;
v_res_419_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_412_, v_y_413_);
stack->m_num = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(lean_object* v_x_420_, lean_object* v_y_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_420_, v_y_421_);
lean_dec(v_y_421_);
lean_dec(v_x_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(lean_object* v___f_424_, lean_object* v_pm_425_, lean_object* v_toPure_426_, lean_object* v_merger_427_, lean_object* v_info_428_){
_start:
{
lean_object* v_subexprPos_429_; lean_object* v___x_430_; 
v_subexprPos_429_ = lean_ctor_get(v_info_428_, 1);
lean_inc(v_subexprPos_429_);
v___x_430_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_424_, v_pm_425_, v_subexprPos_429_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
lean_dec(v_merger_427_);
v___x_431_ = lean_apply_2(v_toPure_426_, lean_box(0), v_info_428_);
return v___x_431_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_433_; 
lean_dec(v_toPure_426_);
v_val_432_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_430_, 1);
v___x_433_ = lean_apply_2(v_merger_427_, v_info_428_, v_val_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object* v_inst_435_, lean_object* v_merger_436_, lean_object* v_pm_437_, lean_object* v_tt_438_){
_start:
{
lean_object* v___f_439_; uint8_t v___y_441_; 
v___f_439_ = ((lean_object*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0));
if (lean_obj_tag(v_pm_437_) == 0)
{
uint8_t v___x_449_; 
v___x_449_ = 0;
v___y_441_ = v___x_449_;
goto v___jp_440_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = 1;
v___y_441_ = v___x_450_;
goto v___jp_440_;
}
v___jp_440_:
{
if (v___y_441_ == 0)
{
lean_object* v_toApplicative_442_; lean_object* v_toPure_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v_toApplicative_442_ = lean_ctor_get(v_inst_435_, 0);
v_toPure_443_ = lean_ctor_get(v_toApplicative_442_, 1);
lean_inc(v_toPure_443_);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1), 5, 4);
lean_closure_set(v___f_444_, 0, v___f_439_);
lean_closure_set(v___f_444_, 1, v_pm_437_);
lean_closure_set(v___f_444_, 2, v_toPure_443_);
lean_closure_set(v___f_444_, 3, v_merger_436_);
v___x_445_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_435_, v___f_444_, v_tt_438_);
return v___x_445_;
}
else
{
lean_object* v_toApplicative_446_; lean_object* v_toPure_447_; lean_object* v___x_448_; 
v_toApplicative_446_ = lean_ctor_get(v_inst_435_, 0);
lean_inc_ref(v_toApplicative_446_);
lean_dec(v_pm_437_);
lean_dec(v_merger_436_);
lean_dec_ref(v_inst_435_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_446_, 1);
lean_inc(v_toPure_447_);
lean_dec_ref(v_toApplicative_446_);
v___x_448_ = lean_apply_2(v_toPure_447_, lean_box(0), v_tt_438_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object* v_m_451_, lean_object* v_00_u03b1_452_, lean_object* v_inst_453_, lean_object* v_merger_454_, lean_object* v_pm_455_, lean_object* v_tt_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(v_inst_453_, v_merger_454_, v_pm_455_, v_tt_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object* v_tt_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_458_);
return v___x_459_;
}
}
lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t v_tag_460_, lean_object* v_c_461_){
_start:
{
lean_object* v_info_462_; lean_object* v_subexprPos_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
v_info_462_ = lean_ctor_get(v_c_461_, 0);
v_subexprPos_463_ = lean_ctor_get(v_c_461_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_c_461_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_c_461_, 2);
lean_dec(v_unused_473_);
v___x_465_ = v_c_461_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_subexprPos_463_);
lean_inc(v_info_462_);
lean_dec(v_c_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = lean_box(v_tag_460_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 2, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_info_462_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_subexprPos_463_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_SubexprInfo_withDiffTag_0interp(lean_interpreter_value* stack)
{
uint8_t v_tag_460_ = stack[0].m_num;
lean_object* v_c_461_ = stack[1].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_460_, v_c_461_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object* v_tag_475_, lean_object* v_c_476_){
_start:
{
uint8_t v_tag_boxed_477_; lean_object* v_res_478_; 
v_tag_boxed_477_ = lean_unbox(v_tag_475_);
v_res_478_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_boxed_477_, v_c_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(lean_object* v_t_479_, lean_object* v_k_480_){
_start:
{
if (lean_obj_tag(v_t_479_) == 0)
{
lean_object* v_k_481_; lean_object* v_v_482_; lean_object* v_l_483_; lean_object* v_r_484_; uint8_t v___x_485_; 
v_k_481_ = lean_ctor_get(v_t_479_, 1);
v_v_482_ = lean_ctor_get(v_t_479_, 2);
v_l_483_ = lean_ctor_get(v_t_479_, 3);
v_r_484_ = lean_ctor_get(v_t_479_, 4);
v___x_485_ = lean_nat_dec_lt(v_k_480_, v_k_481_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_eq(v_k_480_, v_k_481_);
if (v___x_486_ == 0)
{
v_t_479_ = v_r_484_;
goto _start;
}
else
{
lean_object* v___x_488_; 
lean_inc(v_v_482_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v_v_482_);
return v___x_488_;
}
}
else
{
v_t_479_ = v_l_483_;
goto _start;
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(lean_object* v_t_491_, lean_object* v_k_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_491_, v_k_492_);
lean_dec(v_k_492_);
lean_dec(v_t_491_);
return v_res_493_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(lean_object* v_f_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_bs_497_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_499_ == 0)
{
lean_dec_ref(v_f_494_);
return v_bs_497_;
}
else
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_v_500_ = lean_array_uget(v_bs_497_, v_i_496_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_497_, v_i_496_, v___x_501_);
lean_inc_ref(v_f_494_);
v___x_503_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_494_, v_v_500_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_496_, v___x_504_);
v___x_506_ = lean_array_uset(v_bs_x27_502_, v_i_496_, v___x_503_);
v_i_496_ = v___x_505_;
v_bs_497_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_494_ = stack[0].m_obj;
size_t v_sz_495_ = stack[1].m_num;
size_t v_i_496_ = stack[2].m_num;
lean_object* v_bs_497_ = stack[3].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_494_, v_sz_495_, v_i_496_, v_bs_497_);
stack->m_obj
 = v_res_508_;
}
lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(lean_object* v_f_509_, lean_object* v_x_510_){
_start:
{
switch(lean_obj_tag(v_x_510_))
{
case 0:
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_f_509_);
v_a_512_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v_x_510_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v_x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
case 1:
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
v_a_520_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_530_ == 0)
{
v___x_522_ = v_x_510_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v_x_510_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
size_t v_sz_524_; size_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v_sz_524_ = lean_array_size(v_a_520_);
v___x_525_ = ((size_t)0ULL);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_509_, v_sz_524_, v___x_525_, v_a_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_526_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
default: 
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_a_531_);
v_a_532_ = lean_ctor_get(v_x_510_, 1);
lean_inc_ref(v_a_532_);
lean_dec_ref_known(v_x_510_, 2);
v___x_533_ = lean_apply_3(v_f_509_, v_a_531_, v_a_532_, lean_box(0));
return v___x_533_;
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_509_ = stack[0].m_obj;
lean_object* v_x_510_ = stack[1].m_obj;
lean_object* v_res_534_;
v_res_534_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_509_, v_x_510_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg___boxed(lean_object* v_f_535_, lean_object* v_x_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_535_, v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(lean_object* v_f_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_545_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_539_, v_sz_boxed_544_, v_i_boxed_545_, v_bs_542_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_PersistentArray_empty___redArg();
return v___x_547_;
}
}
lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(lean_object* v_infos_548_, lean_object* v_ctx_549_, lean_object* v_x_550_, lean_object* v_subTt_551_){
_start:
{
lean_object* v_fst_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_569_; 
v_fst_553_ = lean_ctor_get(v_x_550_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_x_550_, 1);
lean_dec(v_unused_570_);
v___x_555_ = v_x_550_;
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_fst_553_);
lean_dec(v_x_550_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_infos_548_, v_fst_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
lean_del_object(v___x_555_);
lean_dec(v_fst_553_);
v___x_558_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_549_, v_infos_548_, v_subTt_551_);
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_557_, 1);
v___x_560_ = lean_obj_once(&l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0, &l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0);
lean_inc_ref(v_ctx_549_);
v___x_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_561_, 0, v_ctx_549_);
lean_ctor_set(v___x_561_, 1, v_val_559_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
v___x_562_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_561_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v_fst_553_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
v___x_565_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_549_, v_infos_548_, v_subTt_551_);
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 2);
lean_ctor_set(v___x_555_, 1, v___x_565_);
lean_ctor_set(v___x_555_, 0, v___x_564_);
v___x_567_ = v___x_555_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_548_ = stack[0].m_obj;
lean_object* v_ctx_549_ = stack[1].m_obj;
lean_object* v_x_550_ = stack[2].m_obj;
lean_object* v_subTt_551_ = stack[3].m_obj;
lean_object* v_res_571_;
v_res_571_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(v_infos_548_, v_ctx_549_, v_x_550_, v_subTt_551_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed(lean_object* v_infos_572_, lean_object* v_ctx_573_, lean_object* v_x_574_, lean_object* v_subTt_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(v_infos_572_, v_ctx_573_, v_x_574_, v_subTt_575_);
return v_res_577_;
}
}
lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(lean_object* v_ctx_578_, lean_object* v_infos_579_, lean_object* v_tt_580_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; 
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed), 5, 2);
lean_closure_set(v___f_582_, 0, v_infos_579_);
lean_closure_set(v___f_582_, 1, v_ctx_578_);
v___x_583_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v___f_582_, v_tt_580_);
return v___x_583_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_578_ = stack[0].m_obj;
lean_object* v_infos_579_ = stack[1].m_obj;
lean_object* v_tt_580_ = stack[2].m_obj;
lean_object* v_res_584_;
v_res_584_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_578_, v_infos_579_, v_tt_580_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(lean_object* v_ctx_585_, lean_object* v_infos_586_, lean_object* v_tt_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_585_, v_infos_586_, v_tt_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(lean_object* v_00_u03b4_590_, lean_object* v_t_591_, lean_object* v_k_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_591_, v_k_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(lean_object* v_00_u03b4_594_, lean_object* v_t_595_, lean_object* v_k_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(v_00_u03b4_594_, v_t_595_, v_k_596_);
lean_dec(v_k_596_);
lean_dec(v_t_595_);
return v_res_597_;
}
}
lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(lean_object* v_00_u03b1_598_, lean_object* v_00_u03b2_599_, lean_object* v_f_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_600_, v_x_601_);
return v___x_603_;
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_600_ = stack[2].m_obj;
lean_object* v_x_601_ = stack[3].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(lean_box(0), lean_box(0), v_f_600_, v_x_601_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v_f_607_, lean_object* v_x_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(v_00_u03b1_605_, v_00_u03b2_606_, v_f_607_, v_x_608_);
return v_res_610_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_f_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_bs_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_613_, v_sz_614_, v_i_615_, v_bs_616_);
return v___x_618_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_613_ = stack[2].m_obj;
size_t v_sz_614_ = stack[3].m_num;
size_t v_i_615_ = stack[4].m_num;
lean_object* v_bs_616_ = stack[5].m_obj;
lean_object* v_res_619_;
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(lean_box(0), lean_box(0), v_f_613_, v_sz_614_, v_i_615_, v_bs_616_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_f_622_, lean_object* v_sz_623_, lean_object* v_i_624_, lean_object* v_bs_625_, lean_object* v___y_626_){
_start:
{
size_t v_sz_boxed_627_; size_t v_i_boxed_628_; lean_object* v_res_629_; 
v_sz_boxed_627_ = lean_unbox_usize(v_sz_623_);
lean_dec(v_sz_623_);
v_i_boxed_628_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(v_00_u03b1_620_, v_00_u03b2_621_, v_f_622_, v_sz_boxed_627_, v_i_boxed_628_, v_bs_625_);
return v_res_629_;
}
}
lean_object* l_Lean_Widget_tagCodeInfos(lean_object* v_ctx_630_, lean_object* v_infos_631_, lean_object* v_tt_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_630_, v_infos_631_, v_tt_632_);
return v___x_634_;
}
}
LEAN_EXPORT void l_Lean_Widget_tagCodeInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_630_ = stack[0].m_obj;
lean_object* v_infos_631_ = stack[1].m_obj;
lean_object* v_tt_632_ = stack[2].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lean_Widget_tagCodeInfos(v_ctx_630_, v_infos_631_, v_tt_632_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos___boxed(lean_object* v_ctx_636_, lean_object* v_infos_637_, lean_object* v_tt_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Widget_tagCodeInfos(v_ctx_636_, v_infos_637_, v_tt_638_);
return v_res_640_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(lean_object* v_opts_641_, lean_object* v_opt_642_){
_start:
{
lean_object* v_name_643_; lean_object* v_defValue_644_; lean_object* v_map_645_; lean_object* v___x_646_; 
v_name_643_ = lean_ctor_get(v_opt_642_, 0);
v_defValue_644_ = lean_ctor_get(v_opt_642_, 1);
v_map_645_ = lean_ctor_get(v_opts_641_, 0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_645_, v_name_643_);
if (lean_obj_tag(v___x_646_) == 0)
{
uint8_t v___x_647_; 
v___x_647_ = lean_unbox(v_defValue_644_);
return v___x_647_;
}
else
{
lean_object* v_val_648_; 
v_val_648_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_646_, 1);
if (lean_obj_tag(v_val_648_) == 1)
{
uint8_t v_v_649_; 
v_v_649_ = lean_ctor_get_uint8(v_val_648_, 0);
lean_dec_ref_known(v_val_648_, 0);
return v_v_649_;
}
else
{
uint8_t v___x_650_; 
lean_dec(v_val_648_);
v___x_650_ = lean_unbox(v_defValue_644_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_641_ = stack[0].m_obj;
lean_object* v_opt_642_ = stack[1].m_obj;
uint8_t v_res_651_;
v_res_651_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_641_, v_opt_642_);
stack->m_num = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(lean_object* v_opts_652_, lean_object* v_opt_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_652_, v_opt_653_);
lean_dec_ref(v_opt_653_);
lean_dec_ref(v_opts_652_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(lean_object* v_e_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_Expr_hasMVar(v_e_656_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_e_656_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v_mctx_662_; lean_object* v___x_663_; lean_object* v_fst_664_; lean_object* v_snd_665_; lean_object* v___x_666_; lean_object* v_cache_667_; lean_object* v_zetaDeltaFVarIds_668_; lean_object* v_postponed_669_; lean_object* v_diag_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v___x_661_ = lean_st_ref_get(v___y_657_);
v_mctx_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_ref(v_mctx_662_);
lean_dec(v___x_661_);
v___x_663_ = l_Lean_instantiateMVarsCore(v_mctx_662_, v_e_656_);
v_fst_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_fst_664_);
v_snd_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc(v_snd_665_);
lean_dec_ref(v___x_663_);
v___x_666_ = lean_st_ref_take(v___y_657_);
v_cache_667_ = lean_ctor_get(v___x_666_, 1);
v_zetaDeltaFVarIds_668_ = lean_ctor_get(v___x_666_, 2);
v_postponed_669_ = lean_ctor_get(v___x_666_, 3);
v_diag_670_ = lean_ctor_get(v___x_666_, 4);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_680_);
v___x_672_ = v___x_666_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_diag_670_);
lean_inc(v_postponed_669_);
lean_inc(v_zetaDeltaFVarIds_668_);
lean_inc(v_cache_667_);
lean_dec(v___x_666_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_snd_665_);
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_snd_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_cache_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_zetaDeltaFVarIds_668_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_postponed_669_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_diag_670_);
v___x_675_ = v_reuseFailAlloc_678_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_st_ref_put(v___y_657_, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_fst_664_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_656_ = stack[0].m_obj;
lean_object* v___y_657_ = stack[1].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_656_, v___y_657_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(lean_object* v_e_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_682_, v___y_683_);
lean_dec(v___y_683_);
return v_res_685_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(lean_object* v_e_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_686_, v___y_688_);
return v___x_692_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_686_ = stack[0].m_obj;
lean_object* v___y_687_ = stack[1].m_obj;
lean_object* v___y_688_ = stack[2].m_obj;
lean_object* v___y_689_ = stack[3].m_obj;
lean_object* v___y_690_ = stack[4].m_obj;
lean_object* v_res_693_;
v_res_693_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(v_e_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(lean_object* v_e_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(v_e_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
lean_object* l_Lean_Widget_ppExprTagged(lean_object* v_e_703_, lean_object* v_delab_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_e_711_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_707_);
v___x_716_ = l_Lean_pp_raw;
v___x_717_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(1);
v___x_719_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_703_, v___x_718_, v_delab_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_747_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_747_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_747_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_747_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_fmt_724_; lean_object* v_infos_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_env_730_; lean_object* v___x_731_; lean_object* v_toCold_732_; lean_object* v_mctx_733_; lean_object* v_currNamespace_734_; lean_object* v_openDecls_735_; lean_object* v___x_736_; lean_object* v_ngen_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v_fmt_724_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_fmt_724_);
v_infos_725_ = lean_ctor_get(v_a_720_, 1);
lean_inc(v_infos_725_);
lean_dec(v_a_720_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Std_Format_defWidth;
v___x_728_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_724_, v___x_726_, v___x_727_);
v___x_729_ = lean_st_ref_get(v_a_708_);
v_env_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_env_730_);
lean_dec(v___x_729_);
v___x_731_ = lean_st_ref_get(v_a_706_);
v_toCold_732_ = lean_ctor_get(v_a_707_, 0);
v_mctx_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_mctx_733_);
lean_dec(v___x_731_);
v_currNamespace_734_ = lean_ctor_get(v_toCold_732_, 4);
v_openDecls_735_ = lean_ctor_get(v_toCold_732_, 5);
v___x_736_ = lean_st_ref_get(v_a_708_);
v_ngen_737_ = lean_ctor_get(v___x_736_, 2);
lean_inc_ref(v_ngen_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_735_);
lean_inc(v_currNamespace_734_);
v___x_740_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_740_, 0, v_env_730_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
lean_ctor_set(v___x_740_, 3, v_mctx_733_);
lean_ctor_set(v___x_740_, 4, v___x_715_);
lean_ctor_set(v___x_740_, 5, v_currNamespace_734_);
lean_ctor_set(v___x_740_, 6, v_openDecls_735_);
lean_ctor_set(v___x_740_, 7, v_ngen_737_);
v___x_741_ = ((lean_object*)(l_Lean_Widget_ppExprTagged___closed__0));
v___x_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_738_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
v___x_743_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v___x_742_, v_infos_725_, v___x_728_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_743_);
v___x_745_ = v___x_722_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___x_715_);
v_a_748_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_719_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_719_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
uint8_t v___x_756_; 
lean_dec_ref(v_delab_704_);
v___x_756_ = l_Lean_getPPInstantiateMVars(v___x_715_);
lean_dec_ref(v___x_715_);
if (v___x_756_ == 0)
{
v_e_711_ = v_e_703_;
goto v___jp_710_;
}
else
{
lean_object* v___x_757_; lean_object* v_a_758_; 
v___x_757_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_703_, v_a_706_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
v_e_711_ = v_a_758_;
goto v___jp_710_;
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_expr_dbg_to_string(v_e_711_);
lean_dec_ref(v_e_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_ppExprTagged_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_703_ = stack[0].m_obj;
lean_object* v_delab_704_ = stack[1].m_obj;
lean_object* v_a_705_ = stack[2].m_obj;
lean_object* v_a_706_ = stack[3].m_obj;
lean_object* v_a_707_ = stack[4].m_obj;
lean_object* v_a_708_ = stack[5].m_obj;
lean_object* v_res_759_;
v_res_759_ = l_Lean_Widget_ppExprTagged(v_e_703_, v_delab_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
stack->m_obj
 = v_res_759_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged___boxed(lean_object* v_e_760_, lean_object* v_delab_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Widget_ppExprTagged(v_e_760_, v_delab_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_767_;
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
