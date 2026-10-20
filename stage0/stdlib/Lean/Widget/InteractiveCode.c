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
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Widget_DiffTag_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Widget_DiffTag_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg(lean_object* v_wasChanged_22_){
_start:
{
lean_inc(v_wasChanged_22_);
return v_wasChanged_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(lean_object* v_wasChanged_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_23_);
lean_dec(v_wasChanged_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_wasChanged_28_){
_start:
{
lean_inc(v_wasChanged_28_);
return v_wasChanged_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasChanged_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_wasChanged_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Widget_DiffTag_wasChanged_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_wasChanged_32_);
lean_dec(v_wasChanged_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg(lean_object* v_willChange_35_){
_start:
{
lean_inc(v_willChange_35_);
return v_willChange_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(lean_object* v_willChange_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_36_);
lean_dec(v_willChange_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_willChange_41_){
_start:
{
lean_inc(v_willChange_41_);
return v_willChange_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willChange_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_willChange_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Widget_DiffTag_willChange_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_willChange_45_);
lean_dec(v_willChange_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(lean_object* v_wasDeleted_48_){
_start:
{
lean_inc(v_wasDeleted_48_);
return v_wasDeleted_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(lean_object* v_wasDeleted_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(v_wasDeleted_49_);
lean_dec(v_wasDeleted_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_wasDeleted_54_){
_start:
{
lean_inc(v_wasDeleted_54_);
return v_wasDeleted_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_wasDeleted_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Widget_DiffTag_wasDeleted_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_wasDeleted_58_);
lean_dec(v_wasDeleted_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg(lean_object* v_willDelete_61_){
_start:
{
lean_inc(v_willDelete_61_);
return v_willDelete_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(lean_object* v_willDelete_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_62_);
lean_dec(v_willDelete_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_willDelete_67_){
_start:
{
lean_inc(v_willDelete_67_);
return v_willDelete_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willDelete_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_willDelete_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Widget_DiffTag_willDelete_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_willDelete_71_);
lean_dec(v_willDelete_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg(lean_object* v_wasInserted_74_){
_start:
{
lean_inc(v_wasInserted_74_);
return v_wasInserted_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(lean_object* v_wasInserted_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_75_);
lean_dec(v_wasInserted_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_wasInserted_80_){
_start:
{
lean_inc(v_wasInserted_80_);
return v_wasInserted_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_wasInserted_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_wasInserted_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Lean_Widget_DiffTag_wasInserted_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_wasInserted_84_);
lean_dec(v_wasInserted_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg(lean_object* v_willInsert_87_){
_start:
{
lean_inc(v_willInsert_87_);
return v_willInsert_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(lean_object* v_willInsert_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_88_);
lean_dec(v_willInsert_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_willInsert_93_){
_start:
{
lean_inc(v_willInsert_93_);
return v_willInsert_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_willInsert_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_willInsert_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Lean_Widget_DiffTag_willInsert_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_willInsert_97_);
lean_dec(v_willInsert_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson(uint8_t v_x_118_){
_start:
{
switch(v_x_118_)
{
case 0:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1));
return v___x_119_;
}
case 1:
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3));
return v___x_120_;
}
case 2:
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5));
return v___x_121_;
}
case 3:
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7));
return v___x_122_;
}
case 4:
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9));
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11));
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag_toJson___boxed(lean_object* v_x_125_){
_start:
{
uint8_t v_x_130__boxed_126_; lean_object* v_res_127_; 
v_x_130__boxed_126_ = lean_unbox(v_x_125_);
v_res_127_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_130__boxed_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonDiffTag_fromJson(lean_object* v_json_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Json_getTag_x3f(v_json_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1));
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_val_157_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v___x_155_, 1);
v___x_158_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10));
v___x_159_ = lean_string_dec_eq(v_val_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0));
v___x_161_ = lean_string_dec_eq(v_val_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2));
v___x_163_ = lean_string_dec_eq(v_val_157_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4));
v___x_165_ = lean_string_dec_eq(v_val_157_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6));
v___x_167_ = lean_string_dec_eq(v_val_157_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8));
v___x_169_ = lean_string_dec_eq(v_val_157_, v___x_168_);
lean_dec(v_val_157_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3));
return v___x_170_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4));
return v___x_171_;
}
}
else
{
lean_object* v___x_172_; 
lean_dec(v_val_157_);
v___x_172_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5));
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v_val_157_);
v___x_173_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6));
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v_val_157_);
v___x_174_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7));
return v___x_174_;
}
}
else
{
lean_object* v___x_175_; 
lean_dec(v_val_157_);
v___x_175_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8));
return v___x_175_;
}
}
else
{
lean_object* v___x_176_; 
lean_dec(v_val_157_);
v___x_176_ = ((lean_object*)(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9));
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(lean_object* v_j_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = l_Lean_Json_getObjValD(v_j_179_, v_k_180_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(lean_object* v_j_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_j_183_, v_k_184_);
lean_dec_ref(v_k_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0));
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_x_188_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(lean_object* v_j_192_, lean_object* v_k_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Lean_Json_getObjValD(v_j_192_, v_k_193_);
v___x_195_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(lean_object* v_j_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_j_196_, v_k_197_);
lean_dec_ref(v_k_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(lean_object* v_json_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v___x_203_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc_n(v_json_202_, 2);
v___x_204_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_202_, v___x_203_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_207_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_202_, v___x_206_);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_210_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_json_202_, v___x_209_);
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v_a_205_);
lean_ctor_set(v___x_215_, 1, v_a_208_);
lean_ctor_set(v___x_215_, 2, v_a_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(lean_object* v_k_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v_k_222_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_val_225_ = lean_ctor_get(v_x_223_, 0);
lean_inc(v_val_225_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_k_222_);
lean_ctor_set(v___x_226_, 1, v_val_225_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0___boxed(lean_object* v_k_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v_k_229_, v_x_230_);
lean_dec(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
if (lean_obj_tag(v_a_232_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_array_to_list(v_a_233_);
return v___x_234_;
}
else
{
lean_object* v_head_235_; lean_object* v_tail_236_; lean_object* v___x_237_; 
v_head_235_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_head_235_);
v_tail_236_ = lean_ctor_get(v_a_232_, 1);
lean_inc(v_tail_236_);
lean_dec_ref_known(v_a_232_, 2);
v___x_237_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_233_, v_head_235_);
v_a_232_ = v_tail_236_;
v_a_233_ = v___x_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(lean_object* v_x_241_){
_start:
{
lean_object* v_info_242_; lean_object* v_subexprPos_243_; lean_object* v_diffStatus_x3f_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_info_242_ = lean_ctor_get(v_x_241_, 0);
v_subexprPos_243_ = lean_ctor_get(v_x_241_, 1);
v_diffStatus_x3f_244_ = lean_ctor_get(v_x_241_, 2);
v___x_245_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_info_242_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_info_242_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
lean_inc(v_subexprPos_243_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_subexprPos_243_);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_247_);
v___x_252_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_));
v___x_253_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__0(v___x_252_, v_diffStatus_x3f_244_);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_247_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_251_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_248_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_));
v___x_258_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34__spec__1(v___x_256_, v___x_257_);
v___x_259_ = l_Lean_Json_mkObj(v___x_258_);
lean_dec(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34____boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_info_266_; lean_object* v_subexprPos_267_; lean_object* v_diffStatus_x3f_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_302_; 
v_info_266_ = lean_ctor_get(v_a_264_, 0);
v_subexprPos_267_ = lean_ctor_get(v_a_264_, 1);
v_diffStatus_x3f_268_ = lean_ctor_get(v_a_264_, 2);
v_isSharedCheck_302_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_302_ == 0)
{
v___x_270_ = v_a_264_;
v_isShared_271_ = v_isSharedCheck_302_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_diffStatus_x3f_268_);
lean_inc(v_subexprPos_267_);
lean_inc(v_info_266_);
lean_dec(v_a_264_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_302_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_301_; 
v___x_272_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_273_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_272_, v_info_266_, v_a_265_);
lean_dec_ref(v_info_266_);
v_fst_274_ = lean_ctor_get(v___x_273_, 0);
v_snd_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_301_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_301_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_inc(v_fst_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_301_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_fst_282_; 
v___x_279_ = l_Lean_SubExpr_Pos_toString(v_subexprPos_267_);
lean_dec(v_subexprPos_267_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
if (lean_obj_tag(v_diffStatus_x3f_268_) == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(0);
v_fst_282_ = v___x_290_;
goto v___jp_281_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
v_val_291_ = lean_ctor_get(v_diffStatus_x3f_268_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_diffStatus_x3f_268_);
if (v_isSharedCheck_300_ == 0)
{
v___x_293_ = v_diffStatus_x3f_268_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_val_291_);
lean_dec(v_diffStatus_x3f_268_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = lean_unbox(v_val_291_);
lean_dec(v_val_291_);
v___x_296_ = l_Lean_Widget_instToJsonDiffTag_toJson(v___x_295_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v_fst_282_ = v___x_298_;
goto v___jp_281_;
}
}
}
v___jp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 2, v_fst_282_);
lean_ctor_set(v___x_270_, 1, v___x_280_);
lean_ctor_set(v___x_270_, 0, v_fst_274_);
v___x_284_ = v___x_270_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_fst_274_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_fst_282_);
v___x_284_ = v_reuseFailAlloc_289_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_34_(v___x_284_);
lean_dec_ref(v___x_284_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_285_);
v___x_287_ = v___x_277_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_snd_275_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(lean_object* v_x_303_){
_start:
{
lean_inc_ref(v_x_303_);
return v_x_303_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_306_, lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_inc_ref(v_x_307_);
return v_x_307_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(lean_object* v_00_u03b1_309_, lean_object* v_x_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(v_00_u03b1_309_, v_x_310_, v___y_311_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v_x_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object* v_j_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(v_j_313_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v_info_325_; lean_object* v_subexprPos_326_; lean_object* v_diffStatus_x3f_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_393_; 
v_a_324_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_315_, 1);
v_info_325_ = lean_ctor_get(v_a_324_, 0);
v_subexprPos_326_ = lean_ctor_get(v_a_324_, 1);
v_diffStatus_x3f_327_ = lean_ctor_get(v_a_324_, 2);
v_isSharedCheck_393_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_393_ == 0)
{
v___x_329_ = v_a_324_;
v_isShared_330_ = v_isSharedCheck_393_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_diffStatus_x3f_327_);
lean_inc(v_subexprPos_326_);
lean_inc(v_info_325_);
lean_dec(v_a_324_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_393_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
v___x_332_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_331_, v_info_325_, v_a_314_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_del_object(v___x_329_);
lean_dec(v_diffStatus_x3f_327_);
lean_dec(v_subexprPos_326_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_332_, 1);
v___x_342_ = l_Lean_Json_getStr_x3f(v_subexprPos_326_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_341_);
lean_del_object(v___x_329_);
lean_dec(v_diffStatus_x3f_327_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_342_, 1);
v___x_352_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_a_341_);
lean_del_object(v___x_329_);
lean_dec(v_diffStatus_x3f_327_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_392_; 
v_a_361_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_392_ == 0)
{
v___x_363_ = v___x_352_;
v_isShared_364_ = v_isSharedCheck_392_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_392_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_____do__lift_366_; 
if (lean_obj_tag(v_diffStatus_x3f_327_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
v_____do__lift_366_ = v___x_373_;
goto v___jp_365_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_391_; 
v_val_374_ = lean_ctor_get(v_diffStatus_x3f_327_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_diffStatus_x3f_327_);
if (v_isSharedCheck_391_ == 0)
{
v___x_376_ = v_diffStatus_x3f_327_;
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_diffStatus_x3f_327_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Widget_instFromJsonDiffTag_fromJson(v_val_374_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_376_);
lean_del_object(v___x_363_);
lean_dec(v_a_361_);
lean_dec(v_a_341_);
lean_del_object(v___x_329_);
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_378_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_a_387_);
v___x_389_ = v___x_376_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v_____do__lift_366_ = v___x_389_;
goto v___jp_365_;
}
}
}
}
v___jp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 2, v_____do__lift_366_);
lean_ctor_set(v___x_329_, 1, v_a_361_);
lean_ctor_set(v___x_329_, 0, v_a_341_);
v___x_368_ = v___x_329_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_341_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_____do__lift_366_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_368_);
v___x_370_ = v___x_363_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(lean_object* v_j_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(v_j_394_, v_a_395_);
lean_dec_ref(v_a_395_);
return v_res_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object* v_x_403_, lean_object* v_y_404_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = lean_nat_dec_lt(v_x_403_, v_y_404_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_eq(v_x_403_, v_y_404_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 2;
return v___x_407_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 1;
return v___x_408_;
}
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(lean_object* v_x_410_, lean_object* v_y_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_410_, v_y_411_);
lean_dec(v_y_411_);
lean_dec(v_x_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(lean_object* v___f_414_, lean_object* v_pm_415_, lean_object* v_toPure_416_, lean_object* v_merger_417_, lean_object* v_info_418_){
_start:
{
lean_object* v_subexprPos_419_; lean_object* v___x_420_; 
v_subexprPos_419_ = lean_ctor_get(v_info_418_, 1);
lean_inc(v_subexprPos_419_);
v___x_420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_414_, v_pm_415_, v_subexprPos_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; 
lean_dec(v_merger_417_);
v___x_421_ = lean_apply_2(v_toPure_416_, lean_box(0), v_info_418_);
return v___x_421_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; 
lean_dec(v_toPure_416_);
v_val_422_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_420_, 1);
v___x_423_ = lean_apply_2(v_merger_417_, v_info_418_, v_val_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object* v_inst_425_, lean_object* v_merger_426_, lean_object* v_pm_427_, lean_object* v_tt_428_){
_start:
{
lean_object* v___f_429_; uint8_t v___y_431_; 
v___f_429_ = ((lean_object*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0));
if (lean_obj_tag(v_pm_427_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
v___y_431_ = v___x_439_;
goto v___jp_430_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = 1;
v___y_431_ = v___x_440_;
goto v___jp_430_;
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
lean_object* v_toApplicative_432_; lean_object* v_toPure_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_toApplicative_432_ = lean_ctor_get(v_inst_425_, 0);
v_toPure_433_ = lean_ctor_get(v_toApplicative_432_, 1);
lean_inc(v_toPure_433_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1), 5, 4);
lean_closure_set(v___f_434_, 0, v___f_429_);
lean_closure_set(v___f_434_, 1, v_pm_427_);
lean_closure_set(v___f_434_, 2, v_toPure_433_);
lean_closure_set(v___f_434_, 3, v_merger_426_);
v___x_435_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_425_, v___f_434_, v_tt_428_);
return v___x_435_;
}
else
{
lean_object* v_toApplicative_436_; lean_object* v_toPure_437_; lean_object* v___x_438_; 
v_toApplicative_436_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_toApplicative_436_);
lean_dec(v_pm_427_);
lean_dec(v_merger_426_);
lean_dec_ref(v_inst_425_);
v_toPure_437_ = lean_ctor_get(v_toApplicative_436_, 1);
lean_inc(v_toPure_437_);
lean_dec_ref(v_toApplicative_436_);
v___x_438_ = lean_apply_2(v_toPure_437_, lean_box(0), v_tt_428_);
return v___x_438_;
}
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
lean_object* v_v_489_; lean_object* v___x_490_; lean_object* v_bs_x27_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_v_489_ = lean_array_uget(v_bs_486_, v_i_485_);
v___x_490_ = lean_unsigned_to_nat(0u);
v_bs_x27_491_ = lean_array_uset(v_bs_486_, v_i_485_, v___x_490_);
lean_inc_ref(v_f_483_);
v___x_492_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_483_, v_v_489_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_485_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_491_, v_i_485_, v___x_492_);
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
v___x_534_ = l_Lean_PersistentArray_empty___redArg();
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
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v_fst_540_);
lean_ctor_set(v___x_551_, 2, v___x_550_);
v___x_552_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v_ctx_536_, v_infos_535_, v_subTt_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 2);
lean_ctor_set(v___x_542_, 1, v___x_552_);
lean_ctor_set(v___x_542_, 0, v___x_551_);
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
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
v___x_657_ = lean_st_ref_put(v___y_638_, v___x_656_);
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
lean_object* v_e_690_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_686_);
v___x_695_ = l_Lean_pp_raw;
v___x_696_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(1);
v___x_698_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_682_, v___x_697_, v_delab_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_726_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_726_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_726_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_726_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_fmt_703_; lean_object* v_infos_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_env_709_; lean_object* v___x_710_; lean_object* v_toCold_711_; lean_object* v_mctx_712_; lean_object* v_currNamespace_713_; lean_object* v_openDecls_714_; lean_object* v___x_715_; lean_object* v_ngen_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v_fmt_703_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_fmt_703_);
v_infos_704_ = lean_ctor_get(v_a_699_, 1);
lean_inc(v_infos_704_);
lean_dec(v_a_699_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = l_Std_Format_defWidth;
v___x_707_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_703_, v___x_705_, v___x_706_);
v___x_708_ = lean_st_ref_get(v_a_687_);
v_env_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_708_);
v___x_710_ = lean_st_ref_get(v_a_685_);
v_toCold_711_ = lean_ctor_get(v_a_686_, 0);
v_mctx_712_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_mctx_712_);
lean_dec(v___x_710_);
v_currNamespace_713_ = lean_ctor_get(v_toCold_711_, 4);
v_openDecls_714_ = lean_ctor_get(v_toCold_711_, 5);
v___x_715_ = lean_st_ref_get(v_a_687_);
v_ngen_716_ = lean_ctor_get(v___x_715_, 2);
lean_inc_ref(v_ngen_716_);
lean_dec(v___x_715_);
v___x_717_ = lean_box(0);
v___x_718_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_714_);
lean_inc(v_currNamespace_713_);
v___x_719_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_719_, 0, v_env_709_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
lean_ctor_set(v___x_719_, 3, v_mctx_712_);
lean_ctor_set(v___x_719_, 4, v___x_694_);
lean_ctor_set(v___x_719_, 5, v_currNamespace_713_);
lean_ctor_set(v___x_719_, 6, v_openDecls_714_);
lean_ctor_set(v___x_719_, 7, v_ngen_716_);
v___x_720_ = ((lean_object*)(l_Lean_Widget_ppExprTagged___closed__0));
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_717_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
v___x_722_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(v___x_721_, v_infos_704_, v___x_707_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_722_);
v___x_724_ = v___x_701_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___x_694_);
v_a_727_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_698_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_698_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
uint8_t v___x_735_; 
lean_dec_ref(v_delab_683_);
v___x_735_ = l_Lean_getPPInstantiateMVars(v___x_694_);
lean_dec_ref(v___x_694_);
if (v___x_735_ == 0)
{
v_e_690_ = v_e_682_;
goto v___jp_689_;
}
else
{
lean_object* v___x_736_; lean_object* v_a_737_; 
v___x_736_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_682_, v_a_685_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v_e_690_ = v_a_737_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged___boxed(lean_object* v_e_738_, lean_object* v_delab_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Widget_ppExprTagged(v_e_738_, v_delab_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_745_;
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
