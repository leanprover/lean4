// Lean compiler output
// Module: Lean.Widget.InteractiveDiagnostic
// Imports: public import Lean.Server.Utils public import Lean.Widget.InteractiveGoal public import Init.Data.Array.Subarray.Split import Lean.Linter.UnusedVariables
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_MonadExcept_ofExcept___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_MessageData_maxTraceChildren;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
uint8_t lean_float_beq(double, double);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_join(lean_object*);
extern lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Widget_tagCodeInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instInhabitedTaggedText_default___redArg();
lean_object* l_Lean_Widget_goalToInteractive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_InteractiveGoal_pretty(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object*);
uint8_t l_Lean_MessageData_isUnusedVariableWarning(lean_object*);
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lazy"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strict"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
static const lean_string_object l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
static const lean_string_object l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "LazyTraceChildren"};
static const lean_object* l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Widget_instImpl___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(165, 137, 18, 43, 57, 42, 78, 138)}};
static const lean_object* l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instTypeNameLazyTraceChildren = (const lean_object*)&l_Lean_Widget_instImpl___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0;
static lean_once_cell_t l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedMsgEmbed_default;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedMsgEmbed;
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "goal"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "widget"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "indent"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(206, 200, 13, 200, 175, 144, 184, 75)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cls"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(28, 113, 141, 155, 240, 79, 69, 244)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "msg"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(178, 178, 148, 59, 81, 15, 45, 82)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "collapsed"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(45, 139, 238, 225, 47, 187, 208, 208)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(207, 29, 161, 81, 49, 98, 4, 106)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_array_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wi"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(66, 175, 87, 75, 42, 99, 172, 2)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_array_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value),((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
static const lean_ctor_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value)}};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65__value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object*);
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0_value;
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1_value;
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed___closed__1 = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableMsgEmbed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0_value),((lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__1_value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed___closed__2 = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__2_value;
static const lean_string_object l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "InteractiveMessage"};
static const lean_object* l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__0 = (const lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instImpl___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Widget_instImpl___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 166, 162, 6, 136, 116, 159, 57)}};
static const lean_object* l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1 = (const lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1 = (const lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instTypeNameInteractiveMessage = (const lean_object*)&l_Lean_Widget_instTypeNameInteractiveMessage_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fullRange"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isSilent"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tags"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "leanTags"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "relatedInformation"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
static const lean_string_object l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(lean_object*);
static const lean_closure_object l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_ = (const lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__value;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__19_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__21_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown LeanDiagnosticTag"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown DiagnosticTag"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_;
static const lean_closure_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "expected string or integer diagnostic code, got '"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown DiagnosticSeverity '"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(trace)"};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0;
static lean_once_cell_t l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1;
static lean_once_cell_t l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedEmbedFmt_default;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_diag"};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 80, 229, 227, 38, 203, 204, 166)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__1 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__1_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2_value;
static const lean_array_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0_value;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2_value;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " more entries..."};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__3 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__3_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__3_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__0_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1_value;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__2 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__2_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6_value;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "MessageData.ofLazy: expected MessageData in Dynamic"};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goal "};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__9 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__9_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__10 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0_value;
static const lean_array_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_msgToInteractive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_msgToInteractive___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_msgToInteractive___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractive___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value;
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "goalsAccomplished"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 125, 130, 173, 238, 104, 164, 108)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object*);
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "[error when printing message: "};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__0_value;
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__1 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__1_value;
static const lean_closure_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__2 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__2_value;
static const lean_closure_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__3 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__3_value;
static const lean_array_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__4 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__4_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__4_value)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__5 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__5_value;
static const lean_array_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__6 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__6_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__6_value)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__7 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__7_value;
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Lean 4"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__8 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__8_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__8_value)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__9 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__9_value;
static const lean_array_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__10 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__10_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__10_value)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__11 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__11_value;
static const lean_array_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__12 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__12_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__12_value)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__13 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__13_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___closed__14 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Widget_StrictOrLazy_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_tag_nat(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___impl___boxed(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Widget_StrictOrLazy_ctorIdx___impl(v_00_u03b1_9_, v_00_u03b2_10_, v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v_t_13_);
v___x_16_ = lean_apply_1(v_k_14_, v_a_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Widget_StrictOrLazy_ctorElim(v_00_u03b1_25_, v_00_u03b2_26_, v_motive_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim___redArg(lean_object* v_t_33_, lean_object* v_strict_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_33_, v_strict_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_strict_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_39_, v_strict_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim___redArg(lean_object* v_t_43_, lean_object* v_lazy_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_43_, v_lazy_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_lazy_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_49_, v_lazy_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default___redArg(lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_inst_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v_inst_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy___redArg(lean_object* v_inst_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_inst_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy(lean_object* v_a_61_, lean_object* v_inst_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_inst_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___impl(lean_object* v_x_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_tag_nat(v_x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___impl___boxed(lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___impl(v_x_67_);
lean_dec_ref(v_x_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(lean_object* v_t_69_, lean_object* v_k_70_){
_start:
{
lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_71_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_a_71_);
lean_dec_ref(v_t_69_);
v___x_72_ = lean_apply_1(v_k_70_, v_a_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim(lean_object* v_motive_73_, lean_object* v_ctorIdx_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_k_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_75_, v_k_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___boxed(lean_object* v_motive_79_, lean_object* v_ctorIdx_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_k_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim(v_motive_79_, v_ctorIdx_80_, v_t_81_, v_h_82_, v_k_83_);
lean_dec(v_ctorIdx_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object* v_t_85_, lean_object* v_Lean_Widget_RpcEncodablePacket_strict_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_85_, v_Lean_Widget_RpcEncodablePacket_strict_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_Lean_Widget_RpcEncodablePacket_strict_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_89_, v_Lean_Widget_RpcEncodablePacket_strict_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object* v_t_93_, lean_object* v_Lean_Widget_RpcEncodablePacket_lazy_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_93_, v_Lean_Widget_RpcEncodablePacket_lazy_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_Lean_Widget_RpcEncodablePacket_lazy_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_97_, v_Lean_Widget_RpcEncodablePacket_lazy_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(lean_object* v_json_109_){
_start:
{
lean_object* v___x_110_; 
lean_inc(v_json_109_);
v___x_110_ = l_Lean_Json_getTag_x3f(v_json_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec(v_json_109_);
v___x_111_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_170_; 
v_val_112_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_170_ == 0)
{
v___x_114_ = v___x_110_;
v_isShared_115_ = v_isSharedCheck_170_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v___x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_170_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_box(0);
v___x_117_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
v___x_118_ = lean_string_dec_eq(v_val_112_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
v___x_120_ = lean_string_dec_eq(v_val_112_, v___x_119_);
lean_dec(v_val_112_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_del_object(v___x_114_);
lean_dec(v_json_109_);
v___x_121_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_box(0);
v___x_124_ = l_Lean_Json_parseCtorFields(v_json_109_, v___x_119_, v___x_122_, v___x_123_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_del_object(v___x_114_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_145_; 
v_a_133_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_145_ == 0)
{
v___x_135_ = v___x_124_;
v_isShared_136_ = v_isSharedCheck_145_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_124_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_145_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get(v___x_116_, v_a_133_, v___x_137_);
lean_dec(v_a_133_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 0);
lean_ctor_set(v___x_114_, 0, v___x_138_);
v___x_140_ = v___x_114_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_140_);
v___x_142_ = v___x_135_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_val_112_);
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_box(0);
v___x_148_ = l_Lean_Json_parseCtorFields(v_json_109_, v___x_117_, v___x_146_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_del_object(v___x_114_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_169_; 
v_a_157_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_169_ == 0)
{
v___x_159_ = v___x_148_;
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_148_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get(v___x_116_, v_a_157_, v___x_161_);
lean_dec(v_a_157_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_162_);
v___x_164_ = v___x_114_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_168_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_164_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_174_ = lean_ctor_get(v_x_173_, 0);
v___x_175_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
lean_inc(v_a_174_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_174_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_Json_mkObj(v___x_178_);
lean_dec_ref_known(v___x_178_, 2);
return v___x_179_;
}
else
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_180_ = lean_ctor_get(v_x_173_, 0);
v___x_181_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
lean_inc(v_a_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_180_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_Json_mkObj(v___x_184_);
lean_dec_ref_known(v___x_184_, 2);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38____boxed(lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v_x_186_);
lean_dec_ref(v_x_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_x_192_, lean_object* v_a_193_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v_inst_191_);
v_a_194_ = lean_ctor_get(v_x_192_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_213_ == 0)
{
v___x_196_ = v_x_192_;
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v_x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_rpcEncode_198_; lean_object* v___x_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_212_; 
v_rpcEncode_198_ = lean_ctor_get(v_inst_190_, 0);
lean_inc_ref(v_rpcEncode_198_);
lean_dec_ref(v_inst_190_);
v___x_199_ = lean_apply_2(v_rpcEncode_198_, v_a_194_, v_a_193_);
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
v_snd_201_ = lean_ctor_get(v___x_199_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_212_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_snd_201_);
lean_inc(v_fst_200_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v_fst_200_);
v___x_206_ = v___x_196_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_200_);
v___x_206_ = v_reuseFailAlloc_211_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_206_);
lean_dec_ref(v___x_206_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_207_);
v___x_209_ = v___x_203_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_snd_201_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_233_; 
lean_dec_ref(v_inst_190_);
v_a_214_ = lean_ctor_get(v_x_192_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_233_ == 0)
{
v___x_216_ = v_x_192_;
v_isShared_217_ = v_isSharedCheck_233_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v_x_192_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_233_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_rpcEncode_218_; lean_object* v___x_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_232_; 
v_rpcEncode_218_ = lean_ctor_get(v_inst_191_, 0);
lean_inc_ref(v_rpcEncode_218_);
lean_dec_ref(v_inst_191_);
v___x_219_ = lean_apply_2(v_rpcEncode_218_, v_a_214_, v_a_193_);
v_fst_220_ = lean_ctor_get(v___x_219_, 0);
v_snd_221_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_232_ == 0)
{
v___x_223_ = v___x_219_;
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snd_221_);
lean_inc(v_fst_220_);
lean_dec(v___x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_fst_220_);
v___x_226_ = v___x_216_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_fst_220_);
v___x_226_ = v_reuseFailAlloc_231_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_226_);
lean_dec_ref(v___x_226_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_227_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_snd_221_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_x_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_236_, v_inst_237_, v_x_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_j_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_243_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_inst_242_);
lean_dec_ref(v_inst_241_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_245_, 1);
if (lean_obj_tag(v_a_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_inst_242_);
v_a_255_ = lean_ctor_get(v_a_254_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_254_);
if (v_isSharedCheck_280_ == 0)
{
v___x_257_ = v_a_254_;
v_isShared_258_ = v_isSharedCheck_280_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v_a_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_280_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_rpcDecode_259_; lean_object* v___x_260_; 
v_rpcDecode_259_ = lean_ctor_get(v_inst_241_, 1);
lean_inc_ref(v_rpcDecode_259_);
lean_dec_ref(v_inst_241_);
lean_inc_ref(v_a_244_);
v___x_260_ = lean_apply_2(v_rpcDecode_259_, v_a_255_, v_a_244_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_del_object(v___x_257_);
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
v_a_269_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_279_ == 0)
{
v___x_271_ = v___x_260_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_260_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_a_269_);
v___x_274_ = v___x_257_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_inst_241_);
v_a_281_ = lean_ctor_get(v_a_254_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_a_254_);
if (v_isSharedCheck_306_ == 0)
{
v___x_283_ = v_a_254_;
v_isShared_284_ = v_isSharedCheck_306_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v_a_254_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_306_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_rpcDecode_285_; lean_object* v___x_286_; 
v_rpcDecode_285_ = lean_ctor_get(v_inst_242_, 1);
lean_inc_ref(v_rpcDecode_285_);
lean_dec_ref(v_inst_242_);
lean_inc_ref(v_a_244_);
v___x_286_ = lean_apply_2(v_rpcDecode_285_, v_a_281_, v_a_244_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_del_object(v___x_283_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v_a_295_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_305_ == 0)
{
v___x_297_ = v___x_286_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_286_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_a_295_);
v___x_300_ = v___x_283_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
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
return v___x_302_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_j_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_307_, v_inst_308_, v_j_309_, v_a_310_);
lean_dec_ref(v_a_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_j_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_314_, v_inst_315_, v_j_316_, v_a_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object* v_00_u03b1_319_, lean_object* v_00_u03b2_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_j_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_00_u03b1_319_, v_00_u03b2_320_, v_inst_321_, v_inst_322_, v_j_323_, v_a_324_);
lean_dec_ref(v_a_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object* v_inst_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_inc_ref(v_inst_327_);
lean_inc_ref(v_inst_326_);
v___x_328_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_), 6, 4);
lean_closure_set(v___x_328_, 0, lean_box(0));
lean_closure_set(v___x_328_, 1, lean_box(0));
lean_closure_set(v___x_328_, 2, v_inst_326_);
lean_closure_set(v___x_328_, 3, v_inst_327_);
v___x_329_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed), 6, 4);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, lean_box(0));
lean_closure_set(v___x_329_, 2, v_inst_326_);
lean_closure_set(v___x_329_, 3, v_inst_327_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_inst_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(v_inst_333_, v_inst_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___impl(lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_tag_nat(v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___impl___boxed(lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Widget_MsgEmbed_ctorIdx___impl(v_x_347_);
lean_dec_ref(v_x_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___redArg(lean_object* v_t_349_, lean_object* v_k_350_){
_start:
{
switch(lean_obj_tag(v_t_349_))
{
case 2:
{
lean_object* v_wi_351_; lean_object* v_alt_352_; lean_object* v___x_353_; 
v_wi_351_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_wi_351_);
v_alt_352_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_alt_352_);
lean_dec_ref_known(v_t_349_, 2);
v___x_353_ = lean_apply_2(v_k_350_, v_wi_351_, v_alt_352_);
return v___x_353_;
}
case 3:
{
lean_object* v_indent_354_; lean_object* v_cls_355_; lean_object* v_msg_356_; uint8_t v_collapsed_357_; lean_object* v_children_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_indent_354_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_indent_354_);
v_cls_355_ = lean_ctor_get(v_t_349_, 1);
lean_inc(v_cls_355_);
v_msg_356_ = lean_ctor_get(v_t_349_, 2);
lean_inc_ref(v_msg_356_);
v_collapsed_357_ = lean_ctor_get_uint8(v_t_349_, sizeof(void*)*4);
v_children_358_ = lean_ctor_get(v_t_349_, 3);
lean_inc_ref(v_children_358_);
lean_dec_ref_known(v_t_349_, 4);
v___x_359_ = lean_box(v_collapsed_357_);
v___x_360_ = lean_apply_5(v_k_350_, v_indent_354_, v_cls_355_, v_msg_356_, v___x_359_, v_children_358_);
return v___x_360_;
}
default: 
{
lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_361_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_a_361_);
lean_dec_ref(v_t_349_);
v___x_362_ = lean_apply_1(v_k_350_, v_a_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim(lean_object* v_motive__1_363_, lean_object* v_ctorIdx_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_k_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_365_, v_k_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___boxed(lean_object* v_motive__1_369_, lean_object* v_ctorIdx_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_k_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Widget_MsgEmbed_ctorElim(v_motive__1_369_, v_ctorIdx_370_, v_t_371_, v_h_372_, v_k_373_);
lean_dec(v_ctorIdx_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim___redArg(lean_object* v_t_375_, lean_object* v_expr_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_375_, v_expr_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim(lean_object* v_motive__1_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_expr_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_379_, v_expr_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim___redArg(lean_object* v_t_383_, lean_object* v_goal_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_383_, v_goal_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim(lean_object* v_motive__1_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_goal_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_387_, v_goal_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim___redArg(lean_object* v_t_391_, lean_object* v_widget_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_391_, v_widget_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim(lean_object* v_motive__1_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_widget_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_395_, v_widget_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim___redArg(lean_object* v_t_399_, lean_object* v_trace_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_399_, v_trace_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim(lean_object* v_motive__1_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_trace_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_403_, v_trace_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0(void){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Widget_instInhabitedTaggedText_default___redArg();
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Widget_instInhabitedMsgEmbed_default;
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___impl(lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_tag_nat(v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___impl___boxed(lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___impl(v_x_414_);
lean_dec_ref(v_x_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(lean_object* v_t_416_, lean_object* v_k_417_){
_start:
{
switch(lean_obj_tag(v_t_416_))
{
case 2:
{
lean_object* v_wi_418_; lean_object* v_alt_419_; lean_object* v___x_420_; 
v_wi_418_ = lean_ctor_get(v_t_416_, 0);
lean_inc(v_wi_418_);
v_alt_419_ = lean_ctor_get(v_t_416_, 1);
lean_inc(v_alt_419_);
lean_dec_ref_known(v_t_416_, 2);
v___x_420_ = lean_apply_2(v_k_417_, v_wi_418_, v_alt_419_);
return v___x_420_;
}
case 3:
{
lean_object* v_indent_421_; lean_object* v_cls_422_; lean_object* v_msg_423_; lean_object* v_collapsed_424_; lean_object* v_children_425_; lean_object* v___x_426_; 
v_indent_421_ = lean_ctor_get(v_t_416_, 0);
lean_inc(v_indent_421_);
v_cls_422_ = lean_ctor_get(v_t_416_, 1);
lean_inc(v_cls_422_);
v_msg_423_ = lean_ctor_get(v_t_416_, 2);
lean_inc(v_msg_423_);
v_collapsed_424_ = lean_ctor_get(v_t_416_, 3);
lean_inc(v_collapsed_424_);
v_children_425_ = lean_ctor_get(v_t_416_, 4);
lean_inc(v_children_425_);
lean_dec_ref_known(v_t_416_, 5);
v___x_426_ = lean_apply_5(v_k_417_, v_indent_421_, v_cls_422_, v_msg_423_, v_collapsed_424_, v_children_425_);
return v___x_426_;
}
default: 
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v_t_416_, 0);
lean_inc(v_a_427_);
lean_dec_ref(v_t_416_);
v___x_428_ = lean_apply_1(v_k_417_, v_a_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(lean_object* v_motive_429_, lean_object* v_ctorIdx_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_k_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_431_, v_k_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___boxed(lean_object* v_motive_435_, lean_object* v_ctorIdx_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_k_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(v_motive_435_, v_ctorIdx_436_, v_t_437_, v_h_438_, v_k_439_);
lean_dec(v_ctorIdx_436_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_441_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_441_, v_Lean_Widget_RpcEncodablePacket_expr_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_445_, v_Lean_Widget_RpcEncodablePacket_expr_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_449_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_449_, v_Lean_Widget_RpcEncodablePacket_goal_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_453_, v_Lean_Widget_RpcEncodablePacket_goal_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_457_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_457_, v_Lean_Widget_RpcEncodablePacket_widget_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_460_, lean_object* v_t_461_, lean_object* v_h_462_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_461_, v_Lean_Widget_RpcEncodablePacket_widget_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_465_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_465_, v_Lean_Widget_RpcEncodablePacket_trace_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_469_, v_Lean_Widget_RpcEncodablePacket_trace_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(lean_object* v_json_524_){
_start:
{
lean_object* v___x_525_; 
lean_inc(v_json_524_);
v___x_525_ = l_Lean_Json_getTag_x3f(v_json_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; 
lean_dec(v_json_524_);
v___x_526_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_643_; 
v_val_527_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_643_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_643_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_643_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_box(0);
v___x_532_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_533_ = lean_string_dec_eq(v_val_527_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_535_ = lean_string_dec_eq(v_val_527_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; uint8_t v___x_537_; 
lean_del_object(v___x_529_);
v___x_536_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_537_ = lean_string_dec_eq(v_val_527_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_539_ = lean_string_dec_eq(v_val_527_, v___x_538_);
lean_dec(v_val_527_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec(v_json_524_);
v___x_540_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_unsigned_to_nat(5u);
v___x_542_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_543_ = l_Lean_Json_parseCtorFields(v_json_524_, v___x_538_, v___x_541_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_570_; 
v_a_552_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_570_ == 0)
{
v___x_554_ = v___x_543_;
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_543_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_array_get(v___x_531_, v_a_552_, v___x_556_);
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_array_get(v___x_531_, v_a_552_, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(2u);
v___x_561_ = lean_array_get(v___x_531_, v_a_552_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_array_get(v___x_531_, v_a_552_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(4u);
v___x_565_ = lean_array_get(v___x_531_, v_a_552_, v___x_564_);
lean_dec(v_a_552_);
v___x_566_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_566_, 0, v___x_557_);
lean_ctor_set(v___x_566_, 1, v___x_559_);
lean_ctor_set(v___x_566_, 2, v___x_561_);
lean_ctor_set(v___x_566_, 3, v___x_563_);
lean_ctor_set(v___x_566_, 4, v___x_565_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_566_);
v___x_568_ = v___x_554_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_val_527_);
v___x_571_ = lean_unsigned_to_nat(2u);
v___x_572_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_573_ = l_Lean_Json_parseCtorFields(v_json_524_, v___x_536_, v___x_571_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_594_; 
v_a_582_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_594_ == 0)
{
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_get(v___x_531_, v_a_582_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_array_get(v___x_531_, v_a_582_, v___x_588_);
lean_dec(v_a_582_);
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_590_);
v___x_592_ = v___x_584_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_val_527_);
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_box(0);
v___x_597_ = l_Lean_Json_parseCtorFields(v_json_524_, v___x_534_, v___x_595_, v___x_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_529_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
v_a_606_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_618_ == 0)
{
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_597_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_array_get(v___x_531_, v_a_606_, v___x_610_);
lean_dec(v_a_606_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_611_);
v___x_613_ = v___x_529_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_613_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_val_527_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_box(0);
v___x_621_ = l_Lean_Json_parseCtorFields(v_json_524_, v___x_532_, v___x_619_, v___x_620_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_529_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_642_; 
v_a_630_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_642_ == 0)
{
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_642_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_642_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_array_get(v___x_531_, v_a_630_, v___x_634_);
lean_dec(v_a_630_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_635_);
v___x_637_ = v___x_529_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_637_);
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(lean_object* v_x_646_){
_start:
{
switch(lean_obj_tag(v_x_646_))
{
case 0:
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_647_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v_x_646_, 1);
v___x_648_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_647_);
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_Json_mkObj(v___x_651_);
lean_dec_ref_known(v___x_651_, 2);
return v___x_652_;
}
case 1:
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_653_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v_x_646_, 1);
v___x_654_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_653_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_Json_mkObj(v___x_657_);
lean_dec_ref_known(v___x_657_, 2);
return v___x_658_;
}
case 2:
{
lean_object* v_wi_659_; lean_object* v_alt_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_678_; 
v_wi_659_ = lean_ctor_get(v_x_646_, 0);
v_alt_660_ = lean_ctor_get(v_x_646_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_678_ == 0)
{
v___x_662_ = v_x_646_;
v_isShared_663_ = v_isSharedCheck_678_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_alt_660_);
lean_inc(v_wi_659_);
lean_dec(v_x_646_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_678_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_665_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 0);
lean_ctor_set(v___x_662_, 1, v_wi_659_);
lean_ctor_set(v___x_662_, 0, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_wi_659_);
v___x_667_ = v_reuseFailAlloc_677_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_668_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v_alt_660_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_667_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_Json_mkObj(v___x_672_);
lean_dec_ref_known(v___x_672_, 2);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_664_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_670_);
v___x_676_ = l_Lean_Json_mkObj(v___x_675_);
lean_dec_ref_known(v___x_675_, 2);
return v___x_676_;
}
}
}
default: 
{
lean_object* v_indent_679_; lean_object* v_cls_680_; lean_object* v_msg_681_; lean_object* v_collapsed_682_; lean_object* v_children_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_indent_679_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_indent_679_);
v_cls_680_ = lean_ctor_get(v_x_646_, 1);
lean_inc(v_cls_680_);
v_msg_681_ = lean_ctor_get(v_x_646_, 2);
lean_inc(v_msg_681_);
v_collapsed_682_ = lean_ctor_get(v_x_646_, 3);
lean_inc(v_collapsed_682_);
v_children_683_ = lean_ctor_get(v_x_646_, 4);
lean_inc(v_children_683_);
lean_dec_ref_known(v_x_646_, 5);
v___x_684_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_685_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_indent_679_);
v___x_687_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_cls_680_);
v___x_689_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_msg_681_);
v___x_691_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_collapsed_682_);
v___x_693_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_children_683_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_692_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_690_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_688_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_686_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_Json_mkObj(v___x_700_);
lean_dec_ref_known(v___x_700_, 2);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_684_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_695_);
v___x_704_ = l_Lean_Json_mkObj(v___x_703_);
lean_dec_ref_known(v___x_703_, 2);
return v___x_704_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_710_ == 0)
{
return v_bs_709_;
}
else
{
lean_object* v_v_711_; lean_object* v___x_712_; lean_object* v_bs_x27_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_v_711_ = lean_array_uget(v_bs_709_, v_i_708_);
v___x_712_ = lean_unsigned_to_nat(0u);
v_bs_x27_713_ = lean_array_uset(v_bs_709_, v_i_708_, v___x_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_708_, v___x_714_);
v___x_716_ = lean_array_uset(v_bs_x27_713_, v_i_708_, v_v_711_);
v_i_708_ = v___x_715_;
v_bs_709_ = v___x_716_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_707_ = stack[0].m_num;
size_t v_i_708_ = stack[1].m_num;
lean_object* v_bs_709_ = stack[2].m_obj;
lean_object* v_res_718_;
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_707_, v_i_708_, v_bs_709_);
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_){
_start:
{
size_t v_sz_boxed_722_; size_t v_i_boxed_723_; lean_object* v_res_724_; 
v_sz_boxed_722_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_boxed_722_, v_i_boxed_723_, v_bs_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object* v_a_725_){
_start:
{
size_t v_sz_726_; size_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_sz_726_ = lean_array_size(v_a_725_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_726_, v___x_727_, v_a_725_);
v___x_729_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object* v_x_733_){
_start:
{
switch(lean_obj_tag(v_x_733_))
{
case 0:
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_746_; 
v_a_734_ = lean_ctor_get(v_x_733_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_746_ == 0)
{
v___x_736_ = v_x_733_;
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v_x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 3);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_734_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_Json_mkObj(v___x_743_);
lean_dec_ref_known(v___x_743_, 2);
return v___x_744_;
}
}
}
case 1:
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_a_747_ = lean_ctor_get(v_x_733_, 0);
lean_inc_ref(v_a_747_);
lean_dec_ref_known(v_x_733_, 1);
v___x_748_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_749_ = l_Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(v_a_747_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_Json_mkObj(v___x_752_);
lean_dec_ref_known(v___x_752_, 2);
return v___x_753_;
}
default: 
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_772_; 
v_a_754_ = lean_ctor_get(v_x_733_, 0);
v_a_755_ = lean_ctor_get(v_x_733_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_772_ == 0)
{
v___x_757_ = v_x_733_;
v_isShared_758_ = v_isSharedCheck_772_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_inc(v_a_754_);
lean_dec(v_x_733_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_772_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_759_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_760_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_a_755_);
v___x_761_ = lean_unsigned_to_nat(2u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
v___x_763_ = lean_array_push(v___x_762_, v_a_754_);
v___x_764_ = lean_array_push(v___x_763_, v___x_760_);
v___x_765_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 0);
lean_ctor_set(v___x_757_, 1, v___x_765_);
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_767_ = v___x_757_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_Json_mkObj(v___x_769_);
lean_dec_ref_known(v___x_769_, 2);
return v___x_770_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t v_sz_773_, size_t v_i_774_, lean_object* v_bs_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_lt(v_i_774_, v_sz_773_);
if (v___x_776_ == 0)
{
return v_bs_775_;
}
else
{
lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v_bs_x27_779_; lean_object* v___x_780_; size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v_v_777_ = lean_array_uget(v_bs_775_, v_i_774_);
v___x_778_ = lean_unsigned_to_nat(0u);
v_bs_x27_779_ = lean_array_uset(v_bs_775_, v_i_774_, v___x_778_);
v___x_780_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_v_777_);
v___x_781_ = ((size_t)1ULL);
v___x_782_ = lean_usize_add(v_i_774_, v___x_781_);
v___x_783_ = lean_array_uset(v_bs_x27_779_, v_i_774_, v___x_780_);
v_i_774_ = v___x_782_;
v_bs_775_ = v___x_783_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_773_ = stack[0].m_num;
size_t v_i_774_ = stack[1].m_num;
lean_object* v_bs_775_ = stack[2].m_obj;
lean_object* v_res_785_;
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_773_, v_i_774_, v_bs_775_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object* v_a_786_){
_start:
{
size_t v_sz_787_; size_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_sz_787_ = lean_array_size(v_a_786_);
v___x_788_ = ((size_t)0ULL);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_787_, v___x_788_, v_a_786_);
v___x_790_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object* v_sz_791_, lean_object* v_i_792_, lean_object* v_bs_793_){
_start:
{
size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_sz_boxed_794_ = lean_unbox_usize(v_sz_791_);
lean_dec(v_sz_791_);
v_i_boxed_795_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_boxed_794_, v_i_boxed_795_, v_bs_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(lean_object* v_f_797_, lean_object* v_x_798_, lean_object* v___y_799_){
_start:
{
switch(lean_obj_tag(v_x_798_))
{
case 0:
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_f_797_);
v_a_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___y_799_);
return v___x_806_;
}
}
}
case 1:
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_828_; 
v_a_809_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_828_ == 0)
{
v___x_811_ = v_x_798_;
v_isShared_812_ = v_isSharedCheck_828_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v_x_798_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_828_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_827_; 
v_sz_813_ = lean_array_size(v_a_809_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_797_, v_sz_813_, v___x_814_, v_a_809_, v___y_799_);
v_fst_816_ = lean_ctor_get(v___x_815_, 0);
v_snd_817_ = lean_ctor_get(v___x_815_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_827_ == 0)
{
v___x_819_ = v___x_815_;
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_817_);
lean_inc(v_fst_816_);
lean_dec(v___x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_fst_816_);
v___x_822_ = v___x_811_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_816_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_snd_817_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
default: 
{
lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_850_; 
v_a_829_ = lean_ctor_get(v_x_798_, 0);
v_a_830_ = lean_ctor_get(v_x_798_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_850_ == 0)
{
v___x_832_ = v_x_798_;
v_isShared_833_ = v_isSharedCheck_850_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_inc(v_a_829_);
lean_dec(v_x_798_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_850_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_fst_835_; lean_object* v_snd_836_; lean_object* v___x_837_; lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_849_; 
lean_inc_ref(v_f_797_);
v___x_834_ = lean_apply_2(v_f_797_, v_a_829_, v___y_799_);
v_fst_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_fst_835_);
v_snd_836_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_snd_836_);
lean_dec_ref(v___x_834_);
v___x_837_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_797_, v_a_830_, v_snd_836_);
v_fst_838_ = lean_ctor_get(v___x_837_, 0);
v_snd_839_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_849_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_fst_838_);
lean_ctor_set(v___x_832_, 0, v_fst_835_);
v___x_844_ = v___x_832_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_fst_838_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_snd_839_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(lean_object* v_f_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_bs_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec_ref(v_f_851_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_bs_854_);
lean_ctor_set(v___x_857_, 1, v___y_855_);
return v___x_857_;
}
else
{
lean_object* v_v_858_; lean_object* v___x_859_; lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_862_; lean_object* v_bs_x27_863_; size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v_v_858_ = lean_array_uget_borrowed(v_bs_854_, v_i_853_);
lean_inc(v_v_858_);
lean_inc_ref(v_f_851_);
v___x_859_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_851_, v_v_858_, v___y_855_);
v_fst_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_fst_860_);
v_snd_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_snd_861_);
lean_dec_ref(v___x_859_);
v___x_862_ = lean_unsigned_to_nat(0u);
v_bs_x27_863_ = lean_array_uset(v_bs_854_, v_i_853_, v___x_862_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_853_, v___x_864_);
v___x_866_ = lean_array_uset(v_bs_x27_863_, v_i_853_, v_fst_860_);
v_i_853_ = v___x_865_;
v_bs_854_ = v___x_866_;
v___y_855_ = v_snd_861_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_851_ = stack[0].m_obj;
size_t v_sz_852_ = stack[1].m_num;
size_t v_i_853_ = stack[2].m_num;
lean_object* v_bs_854_ = stack[3].m_obj;
lean_object* v___y_855_ = stack[4].m_obj;
lean_object* v_res_868_;
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_851_, v_sz_852_, v_i_853_, v_bs_854_, v___y_855_);
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg___boxed(lean_object* v_f_869_, lean_object* v_sz_870_, lean_object* v_i_871_, lean_object* v_bs_872_, lean_object* v___y_873_){
_start:
{
size_t v_sz_boxed_874_; size_t v_i_boxed_875_; lean_object* v_res_876_; 
v_sz_boxed_874_ = lean_unbox_usize(v_sz_870_);
lean_dec(v_sz_870_);
v_i_boxed_875_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_869_, v_sz_boxed_874_, v_i_boxed_875_, v_bs_872_, v___y_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(lean_object* v_x_878_, lean_object* v_a_879_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_901_; 
v_a_880_ = lean_ctor_get(v_x_878_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_901_ == 0)
{
v___x_882_ = v_x_878_;
v_isShared_883_ = v_isSharedCheck_901_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v_x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_901_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
size_t v_sz_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v_fst_887_; lean_object* v_snd_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_900_; 
v_sz_884_ = lean_array_size(v_a_880_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_884_, v___x_885_, v_a_880_, v_a_879_);
v_fst_887_ = lean_ctor_get(v___x_886_, 0);
v_snd_888_ = lean_ctor_get(v___x_886_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_900_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snd_888_);
lean_inc(v_fst_887_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(v_fst_887_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_892_);
v___x_894_ = v___x_882_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_899_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_894_);
lean_dec_ref(v___x_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_895_);
v___x_897_ = v___x_890_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_888_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_921_; 
v_a_902_ = lean_ctor_get(v_x_878_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_921_ == 0)
{
v___x_904_ = v_x_878_;
v_isShared_905_ = v_isSharedCheck_921_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v_x_878_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_921_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_920_; 
v___x_906_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_907_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_906_, v_a_902_, v_a_879_);
lean_dec(v_a_902_);
v_fst_908_ = lean_ctor_get(v___x_907_, 0);
v_snd_909_ = lean_ctor_get(v___x_907_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_911_ = v___x_907_;
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v___x_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_920_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v_fst_908_);
v___x_914_ = v___x_904_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_908_);
v___x_914_ = v_reuseFailAlloc_919_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_914_);
lean_dec_ref(v___x_914_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_915_);
v___x_917_ = v___x_911_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_909_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_x_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
switch(lean_obj_tag(v_x_922_))
{
case 0:
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v___x_924_);
v_a_925_ = lean_ctor_get(v_x_922_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_945_ == 0)
{
v___x_927_ = v_x_922_;
v_isShared_928_ = v_isSharedCheck_945_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v_x_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_945_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_944_; 
v___x_929_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_930_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_929_, v_a_925_, v_a_923_);
v_fst_931_ = lean_ctor_get(v___x_930_, 0);
v_snd_932_ = lean_ctor_get(v___x_930_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_944_ == 0)
{
v___x_934_ = v___x_930_;
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_snd_932_);
lean_inc(v_fst_931_);
lean_dec(v___x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_931_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_936_);
v___x_938_ = v___x_927_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_943_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_938_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_939_);
v___x_941_ = v___x_934_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_snd_932_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
case 1:
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___x_924_);
v_a_946_ = lean_ctor_get(v_x_922_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_964_ == 0)
{
v___x_948_ = v_x_922_;
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_x_922_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_963_; 
v___x_950_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_946_, v_a_923_);
v_fst_951_ = lean_ctor_get(v___x_950_, 0);
v_snd_952_ = lean_ctor_get(v___x_950_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_963_ == 0)
{
v___x_954_ = v___x_950_;
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_inc(v_fst_951_);
lean_dec(v___x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_fst_951_);
v___x_957_ = v___x_948_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_fst_951_);
v___x_957_ = v_reuseFailAlloc_962_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_957_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_958_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_snd_952_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
case 2:
{
lean_object* v_wi_965_; lean_object* v_alt_966_; lean_object* v___x_967_; lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_988_; 
v_wi_965_ = lean_ctor_get(v_x_922_, 0);
lean_inc_ref(v_wi_965_);
v_alt_966_ = lean_ctor_get(v_x_922_, 1);
lean_inc_ref(v_alt_966_);
lean_dec_ref_known(v_x_922_, 2);
v___x_967_ = l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_965_, v_a_923_);
v_fst_968_ = lean_ctor_get(v___x_967_, 0);
v_snd_969_ = lean_ctor_get(v___x_967_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_988_ == 0)
{
v___x_971_ = v___x_967_;
v_isShared_972_ = v_isSharedCheck_988_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_snd_969_);
lean_inc(v_fst_968_);
lean_dec(v___x_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_988_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_987_; 
v___x_973_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_924_, v_alt_966_, v_snd_969_);
v_fst_974_ = lean_ctor_get(v___x_973_, 0);
v_snd_975_ = lean_ctor_get(v___x_973_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_987_ == 0)
{
v___x_977_ = v___x_973_;
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v___x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_974_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 2);
lean_ctor_set(v___x_971_, 1, v___x_979_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_968_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_986_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_981_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_982_);
v___x_984_ = v___x_977_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_975_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
default: 
{
lean_object* v_indent_989_; lean_object* v_cls_990_; lean_object* v_msg_991_; uint8_t v_collapsed_992_; lean_object* v_children_993_; lean_object* v___x_994_; lean_object* v_fst_995_; lean_object* v_snd_996_; lean_object* v___x_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1015_; 
v_indent_989_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_indent_989_);
v_cls_990_ = lean_ctor_get(v_x_922_, 1);
lean_inc(v_cls_990_);
v_msg_991_ = lean_ctor_get(v_x_922_, 2);
lean_inc_ref(v_msg_991_);
v_collapsed_992_ = lean_ctor_get_uint8(v_x_922_, sizeof(void*)*4);
v_children_993_ = lean_ctor_get(v_x_922_, 3);
lean_inc_ref(v_children_993_);
lean_dec_ref_known(v_x_922_, 4);
v___x_994_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_924_, v_msg_991_, v_a_923_);
v_fst_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_fst_995_);
v_snd_996_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_996_);
lean_dec_ref(v___x_994_);
v___x_997_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(v_children_993_, v_snd_996_);
v_fst_998_ = lean_ctor_get(v___x_997_, 0);
v_snd_999_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1001_ = v___x_997_;
v_isShared_1002_ = v_isSharedCheck_1015_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v___x_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1015_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1003_ = l_Lean_JsonNumber_fromNat(v_indent_989_);
v___x_1004_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
v___x_1005_ = 1;
v___x_1006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_cls_990_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
v___x_1008_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_995_);
v___x_1009_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1009_, 0, v_collapsed_992_);
v___x_1010_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1004_);
lean_ctor_set(v___x_1010_, 1, v___x_1007_);
lean_ctor_set(v___x_1010_, 2, v___x_1008_);
lean_ctor_set(v___x_1010_, 3, v___x_1009_);
lean_ctor_set(v___x_1010_, 4, v_fst_998_);
v___x_1011_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_1010_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1011_);
v___x_1013_ = v___x_1001_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_999_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(size_t v_sz_1016_, size_t v_i_1017_, lean_object* v_bs_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1017_, v_sz_1016_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_bs_1018_);
lean_ctor_set(v___x_1021_, 1, v___y_1019_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v_v_1023_; lean_object* v___x_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; lean_object* v_bs_x27_1028_; lean_object* v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1022_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
v_v_1023_ = lean_array_uget_borrowed(v_bs_1018_, v_i_1017_);
lean_inc(v_v_1023_);
v___x_1024_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_1022_, v_v_1023_, v___y_1019_);
v_fst_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_fst_1025_);
v_snd_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_snd_1026_);
lean_dec_ref(v___x_1024_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v_bs_x27_1028_ = lean_array_uset(v_bs_1018_, v_i_1017_, v___x_1027_);
v___x_1029_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_1025_);
v___x_1030_ = ((size_t)1ULL);
v___x_1031_ = lean_usize_add(v_i_1017_, v___x_1030_);
v___x_1032_ = lean_array_uset(v_bs_x27_1028_, v_i_1017_, v___x_1029_);
v_i_1017_ = v___x_1031_;
v_bs_1018_ = v___x_1032_;
v___y_1019_ = v_snd_1026_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1016_ = stack[0].m_num;
size_t v_i_1017_ = stack[1].m_num;
lean_object* v_bs_1018_ = stack[2].m_obj;
lean_object* v___y_1019_ = stack[3].m_obj;
lean_object* v_res_1034_;
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_1016_, v_i_1017_, v_bs_1018_, v___y_1019_);
stack->m_obj
 = v_res_1034_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4___boxed(lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_bs_1037_, lean_object* v___y_1038_){
_start:
{
size_t v_sz_boxed_1039_; size_t v_i_boxed_1040_; lean_object* v_res_1041_; 
v_sz_boxed_1039_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_boxed_1039_, v_i_boxed_1040_, v_bs_1037_, v___y_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(lean_object* v_x_1042_){
_start:
{
lean_inc_ref(v_x_1042_);
return v_x_1042_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg___boxed(lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(v_x_1043_);
lean_dec_ref(v_x_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(lean_object* v_00_u03b1_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_){
_start:
{
lean_inc_ref(v_x_1046_);
return v_x_1046_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(v_00_u03b1_1048_, v_x_1049_, v___y_1050_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v_x_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object* v_json_1058_){
_start:
{
lean_object* v___x_1059_; 
lean_inc(v_json_1058_);
v___x_1059_ = l_Lean_Json_getTag_x3f(v_json_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_json_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0));
return v___x_1060_;
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1167_; 
v_val_1061_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1063_ = v___x_1059_;
v_isShared_1064_ = v_isSharedCheck_1167_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_val_1061_);
lean_dec(v___x_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1167_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_1067_ = lean_string_dec_eq(v_val_1061_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
v___x_1069_ = lean_string_dec_eq(v_val_1061_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
lean_del_object(v___x_1063_);
v___x_1070_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_1071_ = lean_string_dec_eq(v_val_1061_, v___x_1070_);
lean_dec(v_val_1061_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_json_1058_);
v___x_1072_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1));
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_unsigned_to_nat(2u);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_Json_parseCtorFields(v_json_1058_, v___x_1070_, v___x_1073_, v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_array_get_borrowed(v___x_1065_, v_a_1084_, v___x_1085_);
lean_inc(v___x_1086_);
v___x_1087_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v___x_1086_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec(v_a_1084_);
return v___x_1087_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_array_get(v___x_1065_, v_a_1084_, v___x_1092_);
lean_dec(v_a_1084_);
v___x_1094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_val_1061_);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_Json_parseCtorFields(v_json_1058_, v___x_1068_, v___x_1099_, v___x_1100_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_del_object(v___x_1063_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_a_1110_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_array_get(v___x_1065_, v_a_1110_, v___x_1111_);
lean_dec(v_a_1110_);
v___x_1113_ = l_Lean_Json_getStr_x3f(v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1063_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1132_; 
v_a_1122_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1124_ = v___x_1113_;
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1113_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 0);
lean_ctor_set(v___x_1063_, 0, v_a_1122_);
v___x_1127_ = v___x_1063_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_val_1061_);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Lean_Json_parseCtorFields(v_json_1058_, v___x_1066_, v___x_1133_, v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_del_object(v___x_1063_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_array_get(v___x_1065_, v_a_1144_, v___x_1145_);
lean_dec(v_a_1144_);
v___x_1147_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1063_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1166_; 
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v_a_1156_);
v___x_1161_ = v___x_1063_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1161_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_bs_1170_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_bs_1170_);
return v___x_1172_;
}
else
{
lean_object* v_v_1173_; lean_object* v___x_1174_; 
v_v_1173_ = lean_array_uget_borrowed(v_bs_1170_, v_i_1169_);
lean_inc(v_v_1173_);
v___x_1174_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_bs_1170_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v_bs_x27_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
v_a_1183_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1184_ = lean_unsigned_to_nat(0u);
v_bs_x27_1185_ = lean_array_uset(v_bs_1170_, v_i_1169_, v___x_1184_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1169_, v___x_1186_);
v___x_1188_ = lean_array_uset(v_bs_x27_1185_, v_i_1169_, v_a_1183_);
v_i_1169_ = v___x_1187_;
v_bs_1170_ = v___x_1188_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1168_ = stack[0].m_num;
size_t v_i_1169_ = stack[1].m_num;
lean_object* v_bs_1170_ = stack[2].m_obj;
lean_object* v_res_1190_;
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_1168_, v_i_1169_, v_bs_1170_);
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 4)
{
lean_object* v_elems_1192_; size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v_elems_1192_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_elems_1192_);
lean_dec_ref_known(v_x_1191_, 1);
v_sz_1193_ = lean_array_size(v_elems_1192_);
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_1193_, v___x_1194_, v_elems_1192_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1197_ = lean_unsigned_to_nat(80u);
v___x_1198_ = l_Lean_Json_pretty(v_x_1191_, v___x_1197_);
v___x_1199_ = lean_string_append(v___x_1196_, v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1201_ = lean_string_append(v___x_1199_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object* v_sz_1203_, lean_object* v_i_1204_, lean_object* v_bs_1205_){
_start:
{
size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1203_);
lean_dec(v_sz_1203_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1204_);
lean_dec(v_i_1204_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_boxed_1206_, v_i_boxed_1207_, v_bs_1205_);
return v_res_1208_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_bs_1211_);
return v___x_1213_;
}
else
{
lean_object* v_v_1214_; lean_object* v___x_1215_; lean_object* v_bs_x27_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v_v_1214_ = lean_array_uget(v_bs_1211_, v_i_1210_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v_bs_x27_1216_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1210_, v___x_1217_);
v___x_1219_ = lean_array_uset(v_bs_x27_1216_, v_i_1210_, v_v_1214_);
v_i_1210_ = v___x_1218_;
v_bs_1211_ = v___x_1219_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1209_ = stack[0].m_num;
size_t v_i_1210_ = stack[1].m_num;
lean_object* v_bs_1211_ = stack[2].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_1209_, v_i_1210_, v_bs_1211_);
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object* v_sz_1222_, lean_object* v_i_1223_, lean_object* v_bs_1224_){
_start:
{
size_t v_sz_boxed_1225_; size_t v_i_boxed_1226_; lean_object* v_res_1227_; 
v_sz_boxed_1225_ = lean_unbox_usize(v_sz_1222_);
lean_dec(v_sz_1222_);
v_i_boxed_1226_ = lean_unbox_usize(v_i_1223_);
lean_dec(v_i_1223_);
v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_boxed_1225_, v_i_boxed_1226_, v_bs_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 4)
{
lean_object* v_elems_1229_; size_t v_sz_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v_elems_1229_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_elems_1229_);
lean_dec_ref_known(v_x_1228_, 1);
v_sz_1230_ = lean_array_size(v_elems_1229_);
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_1230_, v___x_1231_, v_elems_1229_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1233_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1234_ = lean_unsigned_to_nat(80u);
v___x_1235_ = l_Lean_Json_pretty(v_x_1228_, v___x_1234_);
v___x_1236_ = lean_string_append(v___x_1233_, v___x_1235_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1238_ = lean_string_append(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object* v_f_1240_, lean_object* v_x_1241_, lean_object* v___y_1242_){
_start:
{
switch(lean_obj_tag(v_x_1241_))
{
case 0:
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_f_1240_);
v_a_1243_ = lean_ctor_get(v_x_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v_x_1241_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v_x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
}
case 1:
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1278_; 
v_a_1252_ = lean_ctor_get(v_x_1241_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1254_ = v_x_1241_;
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v_x_1241_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
size_t v_sz_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v_sz_1256_ = lean_array_size(v_a_1252_);
v___x_1257_ = ((size_t)0ULL);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1240_, v_sz_1256_, v___x_1257_, v_a_1252_, v___y_1242_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1254_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1277_; 
v_a_1267_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1269_ = v___x_1258_;
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1258_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v_a_1267_);
v___x_1272_ = v___x_1254_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1272_);
v___x_1274_ = v___x_1269_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
default: 
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1306_; 
v_a_1279_ = lean_ctor_get(v_x_1241_, 0);
v_a_1280_ = lean_ctor_get(v_x_1241_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1282_ = v_x_1241_;
v_isShared_1283_ = v_isSharedCheck_1306_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_inc(v_a_1279_);
lean_dec(v_x_1241_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1306_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; 
lean_inc_ref(v_f_1240_);
lean_inc_ref(v___y_1242_);
v___x_1284_ = lean_apply_2(v_f_1240_, v_a_1279_, v___y_1242_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1282_);
lean_dec_ref(v_a_1280_);
lean_dec_ref(v_f_1240_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1294_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1240_, v_a_1280_, v___y_1242_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_dec(v_a_1293_);
lean_del_object(v___x_1282_);
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1305_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1305_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v_a_1295_);
lean_ctor_set(v___x_1282_, 0, v_a_1293_);
v___x_1300_ = v___x_1282_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1293_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object* v_f_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_bs_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v_f_1307_);
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_bs_1310_);
return v___x_1313_;
}
else
{
lean_object* v_v_1314_; lean_object* v___x_1315_; 
v_v_1314_ = lean_array_uget_borrowed(v_bs_1310_, v_i_1309_);
lean_inc(v_v_1314_);
lean_inc_ref(v_f_1307_);
v___x_1315_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1307_, v_v_1314_, v___y_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_bs_1310_);
lean_dec_ref(v_f_1307_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v_bs_x27_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1325_ = lean_unsigned_to_nat(0u);
v_bs_x27_1326_ = lean_array_uset(v_bs_1310_, v_i_1309_, v___x_1325_);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1309_, v___x_1327_);
v___x_1329_ = lean_array_uset(v_bs_x27_1326_, v_i_1309_, v_a_1324_);
v_i_1309_ = v___x_1328_;
v_bs_1310_ = v___x_1329_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1307_ = stack[0].m_obj;
size_t v_sz_1308_ = stack[1].m_num;
size_t v_i_1309_ = stack[2].m_num;
lean_object* v_bs_1310_ = stack[3].m_obj;
lean_object* v___y_1311_ = stack[4].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1307_, v_sz_1308_, v_i_1309_, v_bs_1310_, v___y_1311_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object* v_f_1332_, lean_object* v_sz_1333_, lean_object* v_i_1334_, lean_object* v_bs_1335_, lean_object* v___y_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1333_);
lean_dec(v_sz_1333_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1332_, v_sz_boxed_1337_, v_i_boxed_1338_, v_bs_1335_, v___y_1336_);
lean_dec_ref(v___y_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg___boxed(lean_object* v_f_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1340_, v_x_1341_, v___y_1342_);
lean_dec_ref(v___y_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object* v_j_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1356_; 
v_a_1356_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1347_, 1);
if (lean_obj_tag(v_a_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1393_; 
v_a_1357_ = lean_ctor_get(v_a_1356_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_a_1356_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1359_ = v_a_1356_;
v_isShared_1360_ = v_isSharedCheck_1393_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v_a_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1393_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(v_a_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1359_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1361_, 1);
v_sz_1371_ = lean_array_size(v_a_1370_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_1371_, v___x_1372_, v_a_1370_, v_a_1346_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1359_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1392_; 
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_a_1382_);
v___x_1387_ = v___x_1359_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1419_; 
v_a_1394_ = lean_ctor_get(v_a_1356_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_a_1356_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1396_ = v_a_1356_;
v_isShared_1397_ = v_isSharedCheck_1419_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v_a_1356_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1419_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_1399_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_1398_, v_a_1394_, v_a_1346_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1396_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1418_; 
v_a_1408_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1410_ = v___x_1399_;
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1399_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v_a_1408_);
v___x_1413_ = v___x_1396_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_j_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(v_j_1420_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1432_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
switch(lean_obj_tag(v_a_1431_))
{
case 0:
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___x_1432_);
v_a_1433_ = lean_ctor_get(v_a_1431_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1435_ = v_a_1431_;
v_isShared_1436_ = v_isSharedCheck_1468_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v_a_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1468_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_a_1433_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1435_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1447_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_1448_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1447_, v_a_1446_, v_a_1421_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1435_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1467_; 
v_a_1457_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1459_ = v___x_1448_;
v_isShared_1460_ = v_isSharedCheck_1467_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1448_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1467_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_a_1457_);
v___x_1462_ = v___x_1435_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1462_);
v___x_1464_ = v___x_1459_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v___x_1432_);
v_a_1469_ = lean_ctor_get(v_a_1431_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1471_ = v_a_1431_;
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v_a_1431_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_1469_, v_a_1421_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1471_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1492_; 
v_a_1482_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1484_ = v___x_1473_;
v_isShared_1485_ = v_isSharedCheck_1492_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1473_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1492_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_a_1482_);
v___x_1487_ = v___x_1471_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
case 2:
{
lean_object* v_wi_1494_; lean_object* v_alt_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1539_; 
v_wi_1494_ = lean_ctor_get(v_a_1431_, 0);
v_alt_1495_ = lean_ctor_get(v_a_1431_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1497_ = v_a_1431_;
v_isShared_1498_ = v_isSharedCheck_1539_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_alt_1495_);
lean_inc(v_wi_1494_);
lean_dec(v_a_1431_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1539_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_1494_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1497_);
lean_dec(v_alt_1495_);
lean_dec_ref(v___x_1432_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1509_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_alt_1495_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_a_1508_);
lean_del_object(v___x_1497_);
lean_dec_ref(v___x_1432_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1519_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1432_, v_a_1518_, v_a_1421_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1508_);
lean_del_object(v___x_1497_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1538_; 
v_a_1528_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1530_ = v___x_1519_;
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1519_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1538_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_a_1528_);
lean_ctor_set(v___x_1497_, 0, v_a_1508_);
v___x_1533_ = v___x_1497_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1508_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_indent_1540_; lean_object* v_cls_1541_; lean_object* v_msg_1542_; lean_object* v_collapsed_1543_; lean_object* v_children_1544_; lean_object* v___x_1545_; 
v_indent_1540_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_indent_1540_);
v_cls_1541_ = lean_ctor_get(v_a_1431_, 1);
lean_inc(v_cls_1541_);
v_msg_1542_ = lean_ctor_get(v_a_1431_, 2);
lean_inc(v_msg_1542_);
v_collapsed_1543_ = lean_ctor_get(v_a_1431_, 3);
lean_inc(v_collapsed_1543_);
v_children_1544_ = lean_ctor_get(v_a_1431_, 4);
lean_inc(v_children_1544_);
lean_dec_ref_known(v_a_1431_, 5);
v___x_1545_ = l_Lean_Json_getNat_x3f(v_indent_1540_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_children_1544_);
lean_dec(v_collapsed_1543_);
lean_dec(v_msg_1542_);
lean_dec(v_cls_1541_);
lean_dec_ref(v___x_1432_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1555_ = l_Lean_Name_fromJson_x3f(v_cls_1541_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1554_);
lean_dec(v_children_1544_);
lean_dec(v_collapsed_1543_);
lean_dec(v_msg_1542_);
lean_dec_ref(v___x_1432_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1565_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_msg_1542_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1564_);
lean_dec(v_a_1554_);
lean_dec(v_children_1544_);
lean_dec(v_collapsed_1543_);
lean_dec_ref(v___x_1432_);
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1575_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1432_, v_a_1574_, v_a_1421_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1564_);
lean_dec(v_a_1554_);
lean_dec(v_children_1544_);
lean_dec(v_collapsed_1543_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1585_ = l_Lean_Json_getBool_x3f(v_collapsed_1543_);
lean_dec(v_collapsed_1543_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1584_);
lean_dec(v_a_1564_);
lean_dec(v_a_1554_);
lean_dec(v_children_1544_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1595_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_children_1544_, v_a_1421_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1594_);
lean_dec(v_a_1584_);
lean_dec(v_a_1564_);
lean_dec(v_a_1554_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1613_; 
v_a_1604_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1606_ = v___x_1595_;
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1595_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1611_; 
v___x_1608_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_1608_, 0, v_a_1554_);
lean_ctor_set(v___x_1608_, 1, v_a_1564_);
lean_ctor_set(v___x_1608_, 2, v_a_1584_);
lean_ctor_set(v___x_1608_, 3, v_a_1604_);
v___x_1609_ = lean_unbox(v_a_1594_);
lean_dec(v_a_1594_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*4, v___x_1609_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1608_);
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1608_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed(lean_object* v_j_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(v_j_1614_, v_a_1615_);
lean_dec_ref(v_a_1615_);
return v_res_1616_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t v_sz_1617_, size_t v_i_1618_, lean_object* v_bs_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_usize_dec_lt(v_i_1618_, v_sz_1617_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_bs_1619_);
return v___x_1622_;
}
else
{
lean_object* v_v_1623_; lean_object* v___x_1624_; 
v_v_1623_ = lean_array_uget_borrowed(v_bs_1619_, v_i_1618_);
lean_inc(v_v_1623_);
v___x_1624_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1623_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_bs_1619_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_a_1633_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1634_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
v___x_1635_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1634_, v_a_1633_, v___y_1620_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_bs_1619_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1645_; lean_object* v_bs_x27_1646_; size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1644_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1645_ = lean_unsigned_to_nat(0u);
v_bs_x27_1646_ = lean_array_uset(v_bs_1619_, v_i_1618_, v___x_1645_);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1618_, v___x_1647_);
v___x_1649_ = lean_array_uset(v_bs_x27_1646_, v_i_1618_, v_a_1644_);
v_i_1618_ = v___x_1648_;
v_bs_1619_ = v___x_1649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1617_ = stack[0].m_num;
size_t v_i_1618_ = stack[1].m_num;
lean_object* v_bs_1619_ = stack[2].m_obj;
lean_object* v___y_1620_ = stack[3].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_1617_, v_i_1618_, v_bs_1619_, v___y_1620_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14___boxed(lean_object* v_sz_1652_, lean_object* v_i_1653_, lean_object* v_bs_1654_, lean_object* v___y_1655_){
_start:
{
size_t v_sz_boxed_1656_; size_t v_i_boxed_1657_; lean_object* v_res_1658_; 
v_sz_boxed_1656_ = lean_unbox_usize(v_sz_1652_);
lean_dec(v_sz_1652_);
v_i_boxed_1657_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_res_1658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_boxed_1656_, v_i_boxed_1657_, v_bs_1654_, v___y_1655_);
lean_dec_ref(v___y_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7___boxed(lean_object* v_j_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_j_1659_, v_a_1660_);
lean_dec_ref(v_a_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_f_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_1664_, v_x_1665_, v___y_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_f_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1670_, v_x_1671_, v___y_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_00_u03b2_1675_, lean_object* v_f_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(v_00_u03b1_1674_, v_00_u03b2_1675_, v_f_1676_, v_x_1677_, v___y_1678_);
lean_dec_ref(v___y_1678_);
return v_res_1679_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_f_1682_, size_t v_sz_1683_, size_t v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_1682_, v_sz_1683_, v_i_1684_, v_bs_1685_, v___y_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1682_ = stack[2].m_obj;
size_t v_sz_1683_ = stack[3].m_num;
size_t v_i_1684_ = stack[4].m_num;
lean_object* v_bs_1685_ = stack[5].m_obj;
lean_object* v___y_1686_ = stack[6].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_box(0), lean_box(0), v_f_1682_, v_sz_1683_, v_i_1684_, v_bs_1685_, v___y_1686_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_f_1691_, lean_object* v_sz_1692_, lean_object* v_i_1693_, lean_object* v_bs_1694_, lean_object* v___y_1695_){
_start:
{
size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1692_);
lean_dec(v_sz_1692_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(v_00_u03b1_1689_, v_00_u03b2_1690_, v_f_1691_, v_sz_boxed_1696_, v_i_boxed_1697_, v_bs_1694_, v___y_1695_);
return v_res_1698_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_f_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_bs_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1701_, v_sz_1702_, v_i_1703_, v_bs_1704_, v___y_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1701_ = stack[2].m_obj;
size_t v_sz_1702_ = stack[3].m_num;
size_t v_i_1703_ = stack[4].m_num;
lean_object* v_bs_1704_ = stack[5].m_obj;
lean_object* v___y_1705_ = stack[6].m_obj;
lean_object* v_res_1707_;
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_box(0), lean_box(0), v_f_1701_, v_sz_1702_, v_i_1703_, v_bs_1704_, v___y_1705_);
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_f_1710_, lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_bs_1713_, lean_object* v___y_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(v_00_u03b1_1708_, v_00_u03b2_1709_, v_f_1710_, v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1713_, v___y_1714_);
lean_dec_ref(v___y_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(lean_object* v_j_1731_, lean_object* v_k_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_Lean_Json_getObjValD(v_j_1731_, v_k_1732_);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0___boxed(lean_object* v_j_1735_, lean_object* v_k_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_j_1735_, v_k_1736_);
lean_dec_ref(v_k_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0));
return v___x_1741_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_x_1740_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(lean_object* v_j_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = l_Lean_Json_getObjValD(v_j_1744_, v_k_1745_);
v___x_1747_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1___boxed(lean_object* v_j_1748_, lean_object* v_k_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_j_1748_, v_k_1749_);
lean_dec_ref(v_k_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(lean_object* v_json_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_a_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1803_; 
v___x_1763_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc_n(v_json_1762_, 10);
v___x_1764_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1762_, v___x_1763_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1767_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1766_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1770_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1769_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1773_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1772_);
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1776_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1775_);
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1779_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1778_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1782_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1762_, v___x_1781_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1785_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1784_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1787_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1791_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1790_);
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1794_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1762_, v___x_1793_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1765_);
lean_ctor_set(v___x_1799_, 1, v_a_1768_);
lean_ctor_set(v___x_1799_, 2, v_a_1771_);
lean_ctor_set(v___x_1799_, 3, v_a_1774_);
lean_ctor_set(v___x_1799_, 4, v_a_1777_);
lean_ctor_set(v___x_1799_, 5, v_a_1780_);
lean_ctor_set(v___x_1799_, 6, v_a_1783_);
lean_ctor_set(v___x_1799_, 7, v_a_1786_);
lean_ctor_set(v___x_1799_, 8, v_a_1789_);
lean_ctor_set(v___x_1799_, 9, v_a_1792_);
lean_ctor_set(v___x_1799_, 10, v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(lean_object* v_k_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v___x_1808_; 
lean_dec_ref(v_k_1806_);
v___x_1808_ = lean_box(0);
return v___x_1808_;
}
else
{
lean_object* v_val_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_val_1809_ = lean_ctor_get(v_x_1807_, 0);
lean_inc(v_val_1809_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_k_1806_);
lean_ctor_set(v___x_1810_, 1, v_val_1809_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0___boxed(lean_object* v_k_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v_k_1813_, v_x_1814_);
lean_dec(v_x_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__1(lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
if (lean_obj_tag(v_a_1816_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_array_to_list(v_a_1817_);
return v___x_1818_;
}
else
{
lean_object* v_head_1819_; lean_object* v_tail_1820_; lean_object* v___x_1821_; 
v_head_1819_ = lean_ctor_get(v_a_1816_, 0);
lean_inc(v_head_1819_);
v_tail_1820_ = lean_ctor_get(v_a_1816_, 1);
lean_inc(v_tail_1820_);
lean_dec_ref_known(v_a_1816_, 2);
v___x_1821_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1817_, v_head_1819_);
v_a_1816_ = v_tail_1820_;
v_a_1817_ = v___x_1821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(lean_object* v_x_1825_){
_start:
{
lean_object* v_range_1826_; lean_object* v_fullRange_x3f_1827_; lean_object* v_severity_x3f_1828_; lean_object* v_isSilent_x3f_1829_; lean_object* v_code_x3f_1830_; lean_object* v_source_x3f_1831_; lean_object* v_message_1832_; lean_object* v_tags_x3f_1833_; lean_object* v_leanTags_x3f_1834_; lean_object* v_relatedInformation_x3f_1835_; lean_object* v_data_x3f_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_range_1826_ = lean_ctor_get(v_x_1825_, 0);
v_fullRange_x3f_1827_ = lean_ctor_get(v_x_1825_, 1);
v_severity_x3f_1828_ = lean_ctor_get(v_x_1825_, 2);
v_isSilent_x3f_1829_ = lean_ctor_get(v_x_1825_, 3);
v_code_x3f_1830_ = lean_ctor_get(v_x_1825_, 4);
v_source_x3f_1831_ = lean_ctor_get(v_x_1825_, 5);
v_message_1832_ = lean_ctor_get(v_x_1825_, 6);
v_tags_x3f_1833_ = lean_ctor_get(v_x_1825_, 7);
v_leanTags_x3f_1834_ = lean_ctor_get(v_x_1825_, 8);
v_relatedInformation_x3f_1835_ = lean_ctor_get(v_x_1825_, 9);
v_data_x3f_1836_ = lean_ctor_get(v_x_1825_, 10);
v___x_1837_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_range_1826_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v_range_1826_);
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1842_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1841_, v_fullRange_x3f_1827_);
v___x_1843_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1844_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1843_, v_severity_x3f_1828_);
v___x_1845_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1846_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1845_, v_isSilent_x3f_1829_);
v___x_1847_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1848_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1847_, v_code_x3f_1830_);
v___x_1849_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1850_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1849_, v_source_x3f_1831_);
v___x_1851_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_message_1832_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_message_1832_);
v___x_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1839_);
v___x_1854_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1855_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1854_, v_tags_x3f_1833_);
v___x_1856_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1857_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1856_, v_leanTags_x3f_1834_);
v___x_1858_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1859_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1858_, v_relatedInformation_x3f_1835_);
v___x_1860_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1861_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1860_, v_data_x3f_1836_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1839_);
v___x_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1859_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1857_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1855_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1853_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1850_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1848_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1846_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1844_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1842_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1840_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_));
v___x_1874_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__1(v___x_1872_, v___x_1873_);
v___x_1875_ = l_Lean_Json_mkObj(v___x_1874_);
lean_dec(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58____boxed(lean_object* v_x_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(v_x_1876_);
lean_dec_ref(v_x_1876_);
return v_res_1877_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = l_Lean_JsonNumber_fromNat(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1883_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(2u);
v___x_1885_ = l_Lean_JsonNumber_fromNat(v___x_1884_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1887_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1888_, lean_object* v___y_1889_){
_start:
{
if (v_a_1888_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___y_1889_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___y_1889_);
return v___x_1893_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1888_ = stack[0].m_num;
lean_object* v___y_1889_ = stack[1].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_1888_, v___y_1889_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v_a_boxed_1897_; lean_object* v_res_1898_; 
v_a_boxed_1897_ = lean_unbox(v_a_1895_);
v_res_1898_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1897_, v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_a_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_a_1899_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___y_1900_);
return v___x_1902_;
}
}
lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1903_, lean_object* v___y_1904_){
_start:
{
if (v_a_1903_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___y_1904_);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___y_1904_);
return v___x_1908_;
}
}
}
LEAN_EXPORT void l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1903_ = stack[0].m_num;
lean_object* v___y_1904_ = stack[1].m_obj;
lean_object* v_res_1909_;
v_res_1909_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_1903_, v___y_1904_);
stack->m_obj
 = v_res_1909_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_a_boxed_1912_; lean_object* v_res_1913_; 
v_a_boxed_1912_ = lean_unbox(v_a_1910_);
v_res_1913_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1912_, v___y_1911_);
return v_res_1913_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_unsigned_to_nat(3u);
v___x_1964_ = l_Lean_JsonNumber_fromNat(v___x_1963_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1966_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(4u);
v___x_1968_ = l_Lean_JsonNumber_fromNat(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1970_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_range_1974_; lean_object* v_fullRange_x3f_1975_; lean_object* v_severity_x3f_1976_; lean_object* v_isSilent_x3f_1977_; lean_object* v_code_x3f_1978_; lean_object* v_source_x3f_1979_; lean_object* v_message_1980_; lean_object* v_tags_x3f_1981_; lean_object* v_leanTags_x3f_1982_; lean_object* v_relatedInformation_x3f_1983_; lean_object* v_data_x3f_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2179_; 
v_range_1974_ = lean_ctor_get(v_a_1972_, 0);
v_fullRange_x3f_1975_ = lean_ctor_get(v_a_1972_, 1);
v_severity_x3f_1976_ = lean_ctor_get(v_a_1972_, 2);
v_isSilent_x3f_1977_ = lean_ctor_get(v_a_1972_, 3);
v_code_x3f_1978_ = lean_ctor_get(v_a_1972_, 4);
v_source_x3f_1979_ = lean_ctor_get(v_a_1972_, 5);
v_message_1980_ = lean_ctor_get(v_a_1972_, 6);
v_tags_x3f_1981_ = lean_ctor_get(v_a_1972_, 7);
v_leanTags_x3f_1982_ = lean_ctor_get(v_a_1972_, 8);
v_relatedInformation_x3f_1983_ = lean_ctor_get(v_a_1972_, 9);
v_data_x3f_1984_ = lean_ctor_get(v_a_1972_, 10);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_1972_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_1986_ = v_a_1972_;
v_isShared_1987_ = v_isSharedCheck_2179_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_data_x3f_1984_);
lean_inc(v_relatedInformation_x3f_1983_);
lean_inc(v_leanTags_x3f_1982_);
lean_inc(v_tags_x3f_1981_);
lean_inc(v_message_1980_);
lean_inc(v_source_x3f_1979_);
lean_inc(v_code_x3f_1978_);
lean_inc(v_isSilent_x3f_1977_);
lean_inc(v_severity_x3f_1976_);
lean_inc(v_fullRange_x3f_1975_);
lean_inc(v_range_1974_);
lean_dec(v_a_1972_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2179_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___f_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v_fst_2096_; lean_object* v_snd_2097_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v_fst_2112_; lean_object* v_snd_2113_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v___y_2140_; lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___y_2155_; lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v_fst_2160_; lean_object* v_snd_2161_; 
v___f_1988_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1989_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1990_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_1991_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1974_);
if (lean_obj_tag(v_fullRange_x3f_1975_) == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_box(0);
v_fst_2160_ = v___x_2169_;
v_snd_2161_ = v_a_1973_;
goto v___jp_2159_;
}
else
{
lean_object* v_val_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2178_; 
v_val_2170_ = lean_ctor_get(v_fullRange_x3f_1975_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_fullRange_x3f_1975_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2172_ = v_fullRange_x3f_1975_;
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_val_2170_);
lean_dec(v_fullRange_x3f_1975_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_2170_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2174_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
v_fst_2160_ = v___x_2176_;
v_snd_2161_ = v_a_1973_;
goto v___jp_2159_;
}
}
}
v___jp_1992_:
{
lean_object* v___x_2004_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 9, v_fst_2001_);
lean_ctor_set(v___x_1986_, 8, v___y_1996_);
lean_ctor_set(v___x_1986_, 7, v___y_1994_);
lean_ctor_set(v___x_1986_, 6, v___y_1993_);
lean_ctor_set(v___x_1986_, 5, v___y_2000_);
lean_ctor_set(v___x_1986_, 4, v___y_1997_);
lean_ctor_set(v___x_1986_, 3, v___y_1998_);
lean_ctor_set(v___x_1986_, 2, v___y_1999_);
lean_ctor_set(v___x_1986_, 1, v___y_1995_);
lean_ctor_set(v___x_1986_, 0, v___x_1991_);
v___x_2004_ = v___x_1986_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___y_1995_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v___y_1999_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v___y_1998_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v___y_1997_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v___y_2000_);
lean_ctor_set(v_reuseFailAlloc_2007_, 6, v___y_1993_);
lean_ctor_set(v_reuseFailAlloc_2007_, 7, v___y_1994_);
lean_ctor_set(v_reuseFailAlloc_2007_, 8, v___y_1996_);
lean_ctor_set(v_reuseFailAlloc_2007_, 9, v_fst_2001_);
lean_ctor_set(v_reuseFailAlloc_2007_, 10, v_data_x3f_1984_);
v___x_2004_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(v___x_2004_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_snd_2002_);
return v___x_2006_;
}
}
v___jp_2008_:
{
lean_object* v___x_2018_; 
v___x_2018_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_relatedInformation_x3f_1983_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
v___y_1993_ = v___y_2009_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2011_;
v___y_1996_ = v_fst_2016_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2013_;
v___y_1999_ = v___y_2012_;
v___y_2000_ = v___y_2015_;
v_fst_2001_ = v___x_2019_;
v_snd_2002_ = v_snd_2017_;
goto v___jp_1992_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2035_; 
v_val_2020_ = lean_ctor_get(v_relatedInformation_x3f_1983_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_relatedInformation_x3f_1983_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2022_ = v_relatedInformation_x3f_1983_;
v_isShared_2023_ = v_isSharedCheck_2035_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v_relatedInformation_x3f_1983_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2035_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
size_t v_sz_2024_; size_t v___x_2025_; lean_object* v___x_7261__overap_2026_; lean_object* v___x_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v_sz_2024_ = lean_array_size(v_val_2020_);
v___x_2025_ = ((size_t)0ULL);
v___x_7261__overap_2026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2018_, v___f_1989_, v_sz_2024_, v___x_2025_, v_val_2020_);
v___x_2027_ = lean_apply_1(v___x_7261__overap_2026_, v_snd_2017_);
v_fst_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v___x_2027_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2027_);
v___x_2030_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2031_ = l_Lean_Array_toJson___redArg(v___x_2030_, v_fst_2028_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2031_);
v___x_2033_ = v___x_2022_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v___y_1993_ = v___y_2009_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2011_;
v___y_1996_ = v_fst_2016_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2013_;
v___y_1999_ = v___y_2012_;
v___y_2000_ = v___y_2015_;
v_fst_2001_ = v___x_2033_;
v_snd_2002_ = v_snd_2029_;
goto v___jp_1992_;
}
}
}
}
v___jp_2036_:
{
lean_object* v___x_2045_; 
v___x_2045_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_leanTags_x3f_1982_) == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_box(0);
v___y_2009_ = v___y_2037_;
v___y_2010_ = v_fst_2043_;
v___y_2011_ = v___y_2038_;
v___y_2012_ = v___y_2041_;
v___y_2013_ = v___y_2040_;
v___y_2014_ = v___y_2039_;
v___y_2015_ = v___y_2042_;
v_fst_2016_ = v___x_2046_;
v_snd_2017_ = v_snd_2044_;
goto v___jp_2008_;
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2062_; 
v_val_2047_ = lean_ctor_get(v_leanTags_x3f_1982_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_leanTags_x3f_1982_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2049_ = v_leanTags_x3f_1982_;
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_dec(v_leanTags_x3f_1982_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
size_t v_sz_2051_; size_t v___x_2052_; lean_object* v___x_7285__overap_2053_; lean_object* v___x_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v_sz_2051_ = lean_array_size(v_val_2047_);
v___x_2052_ = ((size_t)0ULL);
v___x_7285__overap_2053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2045_, v___f_1988_, v_sz_2051_, v___x_2052_, v_val_2047_);
v___x_2054_ = lean_apply_1(v___x_7285__overap_2053_, v_snd_2044_);
v_fst_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_fst_2055_);
v_snd_2056_ = lean_ctor_get(v___x_2054_, 1);
lean_inc(v_snd_2056_);
lean_dec_ref(v___x_2054_);
v___x_2057_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2058_ = l_Lean_Array_toJson___redArg(v___x_2057_, v_fst_2055_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2058_);
v___x_2060_ = v___x_2049_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v___y_2009_ = v___y_2037_;
v___y_2010_ = v_fst_2043_;
v___y_2011_ = v___y_2038_;
v___y_2012_ = v___y_2041_;
v___y_2013_ = v___y_2040_;
v___y_2014_ = v___y_2039_;
v___y_2015_ = v___y_2042_;
v_fst_2016_ = v___x_2060_;
v_snd_2017_ = v_snd_2056_;
goto v___jp_2008_;
}
}
}
}
v___jp_2063_:
{
lean_object* v_rpcEncode_2070_; lean_object* v___x_2071_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2074_; 
v_rpcEncode_2070_ = lean_ctor_get(v_inst_1971_, 0);
lean_inc_ref(v_rpcEncode_2070_);
lean_dec_ref(v_inst_1971_);
v___x_2071_ = lean_apply_2(v_rpcEncode_2070_, v_message_1980_, v_snd_2069_);
v_fst_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_fst_2072_);
v_snd_2073_ = lean_ctor_get(v___x_2071_, 1);
lean_inc(v_snd_2073_);
lean_dec_ref(v___x_2071_);
v___x_2074_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_tags_x3f_1981_) == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_box(0);
v___y_2037_ = v_fst_2072_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2067_;
v___y_2040_ = v___y_2066_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v_fst_2068_;
v_fst_2043_ = v___x_2075_;
v_snd_2044_ = v_snd_2073_;
goto v___jp_2036_;
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2091_; 
v_val_2076_ = lean_ctor_get(v_tags_x3f_1981_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_tags_x3f_1981_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2078_ = v_tags_x3f_1981_;
v_isShared_2079_ = v_isSharedCheck_2091_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_val_2076_);
lean_dec(v_tags_x3f_1981_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2091_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_7309__overap_2082_; lean_object* v___x_2083_; lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v_sz_2080_ = lean_array_size(v_val_2076_);
v___x_2081_ = ((size_t)0ULL);
v___x_7309__overap_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2074_, v___f_1990_, v_sz_2080_, v___x_2081_, v_val_2076_);
v___x_2083_ = lean_apply_1(v___x_7309__overap_2082_, v_snd_2073_);
v_fst_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_fst_2084_);
v_snd_2085_ = lean_ctor_get(v___x_2083_, 1);
lean_inc(v_snd_2085_);
lean_dec_ref(v___x_2083_);
v___x_2086_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2087_ = l_Lean_Array_toJson___redArg(v___x_2086_, v_fst_2084_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2087_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v___y_2037_ = v_fst_2072_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2067_;
v___y_2040_ = v___y_2066_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v_fst_2068_;
v_fst_2043_ = v___x_2089_;
v_snd_2044_ = v_snd_2085_;
goto v___jp_2036_;
}
}
}
}
v___jp_2092_:
{
if (lean_obj_tag(v_source_x3f_1979_) == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_box(0);
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2095_;
v___y_2066_ = v___y_2094_;
v___y_2067_ = v_fst_2096_;
v_fst_2068_ = v___x_2098_;
v_snd_2069_ = v_snd_2097_;
goto v___jp_2063_;
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_val_2099_ = lean_ctor_get(v_source_x3f_1979_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_source_x3f_1979_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2101_ = v_source_x3f_1979_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_val_2099_);
lean_dec(v_source_x3f_1979_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_val_2099_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2095_;
v___y_2066_ = v___y_2094_;
v___y_2067_ = v_fst_2096_;
v_fst_2068_ = v___x_2105_;
v_snd_2069_ = v_snd_2097_;
goto v___jp_2063_;
}
}
}
}
v___jp_2108_:
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_fst_2112_);
v___y_2093_ = v___y_2109_;
v___y_2094_ = v___y_2111_;
v___y_2095_ = v___y_2110_;
v_fst_2096_ = v___x_2114_;
v_snd_2097_ = v_snd_2113_;
goto v___jp_2092_;
}
v___jp_2115_:
{
if (lean_obj_tag(v_code_x3f_1978_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_box(0);
v___y_2093_ = v___y_2116_;
v___y_2094_ = v_fst_2118_;
v___y_2095_ = v___y_2117_;
v_fst_2096_ = v___x_2120_;
v_snd_2097_ = v_snd_2119_;
goto v___jp_2092_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v_code_x3f_1978_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v_code_x3f_1978_, 1);
if (lean_obj_tag(v_val_2121_) == 0)
{
lean_object* v_i_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_i_2122_ = lean_ctor_get(v_val_2121_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_val_2121_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2124_ = v_val_2121_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_i_2122_);
lean_dec(v_val_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = l_Lean_JsonNumber_fromInt(v_i_2122_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 2);
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
v___y_2109_ = v___y_2116_;
v___y_2110_ = v___y_2117_;
v___y_2111_ = v_fst_2118_;
v_fst_2112_ = v___x_2128_;
v_snd_2113_ = v_snd_2119_;
goto v___jp_2108_;
}
}
}
else
{
lean_object* v_s_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_s_2131_ = lean_ctor_get(v_val_2121_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_val_2121_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v_val_2121_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_s_2131_);
lean_dec(v_val_2121_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 3);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_s_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
v___y_2109_ = v___y_2116_;
v___y_2110_ = v___y_2117_;
v___y_2111_ = v_fst_2118_;
v_fst_2112_ = v___x_2136_;
v_snd_2113_ = v_snd_2119_;
goto v___jp_2108_;
}
}
}
}
}
v___jp_2139_:
{
if (lean_obj_tag(v_isSilent_x3f_1977_) == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_box(0);
v___y_2116_ = v___y_2140_;
v___y_2117_ = v_fst_2141_;
v_fst_2118_ = v___x_2143_;
v_snd_2119_ = v_snd_2142_;
goto v___jp_2115_;
}
else
{
lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2153_; 
v_val_2144_ = lean_ctor_get(v_isSilent_x3f_1977_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_isSilent_x3f_1977_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2146_ = v_isSilent_x3f_1977_;
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_dec(v_isSilent_x3f_1977_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2151_; 
v___x_2148_ = lean_alloc_ctor(1, 0, 1);
v___x_2149_ = lean_unbox(v_val_2144_);
lean_dec(v_val_2144_);
lean_ctor_set_uint8(v___x_2148_, 0, v___x_2149_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2148_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
v___y_2116_ = v___y_2140_;
v___y_2117_ = v_fst_2141_;
v_fst_2118_ = v___x_2151_;
v_snd_2119_ = v_snd_2142_;
goto v___jp_2115_;
}
}
}
}
v___jp_2154_:
{
lean_object* v___x_2158_; 
lean_inc(v_fst_2156_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_fst_2156_);
v___y_2140_ = v___y_2155_;
v_fst_2141_ = v___x_2158_;
v_snd_2142_ = v_snd_2157_;
goto v___jp_2139_;
}
v___jp_2159_:
{
if (lean_obj_tag(v_severity_x3f_1976_) == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_box(0);
v___y_2140_ = v_fst_2160_;
v_fst_2141_ = v___x_2162_;
v_snd_2142_ = v_snd_2161_;
goto v___jp_2139_;
}
else
{
lean_object* v_val_2163_; uint8_t v___x_2164_; 
v_val_2163_ = lean_ctor_get(v_severity_x3f_1976_, 0);
lean_inc(v_val_2163_);
lean_dec_ref_known(v_severity_x3f_1976_, 1);
v___x_2164_ = lean_unbox(v_val_2163_);
lean_dec(v_val_2163_);
switch(v___x_2164_)
{
case 0:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2155_ = v_fst_2160_;
v_fst_2156_ = v___x_2165_;
v_snd_2157_ = v_snd_2161_;
goto v___jp_2154_;
}
case 1:
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2155_ = v_fst_2160_;
v_fst_2156_ = v___x_2166_;
v_snd_2157_ = v_snd_2161_;
goto v___jp_2154_;
}
case 2:
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2155_ = v_fst_2160_;
v_fst_2156_ = v___x_2167_;
v_snd_2157_ = v_snd_2161_;
goto v___jp_2154_;
}
default: 
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2155_ = v_fst_2160_;
v_fst_2156_ = v___x_2168_;
v_snd_2157_ = v_snd_2161_;
goto v___jp_2154_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2180_, lean_object* v_inst_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2181_, v_a_2182_, v_a_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2185_, lean_object* v___x_2186_, lean_object* v_j_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_10463__overap_2190_; lean_object* v___x_2191_; 
v___x_2189_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_j_2187_);
v___x_10463__overap_2190_ = l_MonadExcept_ofExcept___redArg(v___x_2185_, v___x_2186_, v___x_2189_);
lean_inc_ref(v___y_2188_);
v___x_2191_ = lean_apply_1(v___x_10463__overap_2190_, v___y_2188_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2192_, lean_object* v___x_2193_, lean_object* v_j_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2192_, v___x_2193_, v_j_2194_, v___y_2195_);
lean_dec_ref(v___y_2195_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v_j_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Json_getNat_x3f(v_j_2208_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_dec_eq(v_a_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_unsigned_to_nat(2u);
v___x_2219_ = lean_nat_dec_eq(v_a_2215_, v___x_2218_);
lean_dec(v_a_2215_);
if (v___x_2219_ == 0)
{
goto v___jp_2210_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_10479__overap_2221_; lean_object* v___x_2222_; 
v___x_2220_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10479__overap_2221_ = l_MonadExcept_ofExcept___redArg(v___x_2206_, v___x_2207_, v___x_2220_);
lean_inc_ref(v___y_2209_);
v___x_2222_ = lean_apply_1(v___x_10479__overap_2221_, v___y_2209_);
return v___x_2222_;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_10482__overap_2224_; lean_object* v___x_2225_; 
lean_dec(v_a_2215_);
v___x_2223_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10482__overap_2224_ = l_MonadExcept_ofExcept___redArg(v___x_2206_, v___x_2207_, v___x_2223_);
lean_inc_ref(v___y_2209_);
v___x_2225_ = lean_apply_1(v___x_10482__overap_2224_, v___y_2209_);
return v___x_2225_;
}
}
else
{
lean_dec_ref(v___x_2214_);
goto v___jp_2210_;
}
v___jp_2210_:
{
lean_object* v___x_2211_; lean_object* v___x_10470__overap_2212_; lean_object* v___x_2213_; 
v___x_2211_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10470__overap_2212_ = l_MonadExcept_ofExcept___redArg(v___x_2206_, v___x_2207_, v___x_2211_);
lean_inc_ref(v___y_2209_);
v___x_2213_ = lean_apply_1(v___x_10470__overap_2212_, v___y_2209_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2226_, lean_object* v___x_2227_, lean_object* v_j_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2226_, v___x_2227_, v_j_2228_, v___y_2229_);
lean_dec_ref(v___y_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_j_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Json_getNat_x3f(v_j_2242_);
if (lean_obj_tag(v___x_2248_) == 1)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_dec_eq(v_a_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_unsigned_to_nat(2u);
v___x_2253_ = lean_nat_dec_eq(v_a_2249_, v___x_2252_);
lean_dec(v_a_2249_);
if (v___x_2253_ == 0)
{
goto v___jp_2244_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_10498__overap_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10498__overap_2255_ = l_MonadExcept_ofExcept___redArg(v___x_2240_, v___x_2241_, v___x_2254_);
lean_inc_ref(v___y_2243_);
v___x_2256_ = lean_apply_1(v___x_10498__overap_2255_, v___y_2243_);
return v___x_2256_;
}
}
else
{
lean_object* v___x_2257_; lean_object* v___x_10501__overap_2258_; lean_object* v___x_2259_; 
lean_dec(v_a_2249_);
v___x_2257_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10501__overap_2258_ = l_MonadExcept_ofExcept___redArg(v___x_2240_, v___x_2241_, v___x_2257_);
lean_inc_ref(v___y_2243_);
v___x_2259_ = lean_apply_1(v___x_10501__overap_2258_, v___y_2243_);
return v___x_2259_;
}
}
else
{
lean_dec_ref(v___x_2248_);
goto v___jp_2244_;
}
v___jp_2244_:
{
lean_object* v___x_2245_; lean_object* v___x_10489__overap_2246_; lean_object* v___x_2247_; 
v___x_2245_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10489__overap_2246_ = l_MonadExcept_ofExcept___redArg(v___x_2240_, v___x_2241_, v___x_2245_);
lean_inc_ref(v___y_2243_);
v___x_2247_ = lean_apply_1(v___x_10489__overap_2246_, v___y_2243_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v_j_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2260_, v___x_2261_, v_j_2262_, v___y_2263_);
lean_dec_ref(v___y_2263_);
return v_res_2264_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2266_ = l_ReaderT_instMonad___redArg(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___f_2268_; 
v___x_2267_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2268_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2268_, 0, v___x_2267_);
return v___f_2268_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___f_2270_; 
v___x_2269_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2270_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
return v___f_2270_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___f_2272_; 
v___x_2271_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2272_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_2272_, 0, v___x_2271_);
return v___f_2272_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___f_2274_; 
v___x_2273_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2274_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_2274_, 0, v___x_2273_);
return v___f_2274_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2276_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_2276_, 0, lean_box(0));
lean_closure_set(v___x_2276_, 1, lean_box(0));
lean_closure_set(v___x_2276_, 2, v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___f_2277_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2278_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___f_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2281_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_2281_, 0, lean_box(0));
lean_closure_set(v___x_2281_, 1, lean_box(0));
lean_closure_set(v___x_2281_, 2, v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___f_2282_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2283_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2284_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2285_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2286_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___x_2285_);
lean_ctor_set(v___x_2287_, 2, v___f_2284_);
lean_ctor_set(v___x_2287_, 3, v___f_2283_);
lean_ctor_set(v___x_2287_, 4, v___f_2282_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2289_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_2289_, 0, lean_box(0));
lean_closure_set(v___x_2289_, 1, lean_box(0));
lean_closure_set(v___x_2289_, 2, v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2291_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2294_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_2294_, 0, lean_box(0));
lean_closure_set(v___x_2294_, 1, lean_box(0));
lean_closure_set(v___x_2294_, 2, v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_2310_, lean_object* v_j_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(v_j_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_inst_2310_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2755_; 
v_a_2322_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2324_ = v___x_2313_;
v_isShared_2325_ = v_isSharedCheck_2755_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2313_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2755_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_toApplicative_2328_; lean_object* v_toPure_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_range_2334_; lean_object* v_fullRange_x3f_2335_; lean_object* v_severity_x3f_2336_; lean_object* v_isSilent_x3f_2337_; lean_object* v_code_x3f_2338_; lean_object* v_source_x3f_2339_; lean_object* v_message_2340_; lean_object* v_tags_x3f_2341_; lean_object* v_leanTags_x3f_2342_; lean_object* v_relatedInformation_x3f_2343_; lean_object* v_data_x3f_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2754_; 
v___x_2326_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2327_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v_toApplicative_2328_ = lean_ctor_get(v___x_2326_, 0);
v_toPure_2329_ = lean_ctor_get(v_toApplicative_2328_, 1);
lean_inc(v_toPure_2329_);
v___f_2330_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2330_, 0, v_toPure_2329_);
v___x_2331_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___f_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2332_);
v_range_2334_ = lean_ctor_get(v_a_2322_, 0);
v_fullRange_x3f_2335_ = lean_ctor_get(v_a_2322_, 1);
v_severity_x3f_2336_ = lean_ctor_get(v_a_2322_, 2);
v_isSilent_x3f_2337_ = lean_ctor_get(v_a_2322_, 3);
v_code_x3f_2338_ = lean_ctor_get(v_a_2322_, 4);
v_source_x3f_2339_ = lean_ctor_get(v_a_2322_, 5);
v_message_2340_ = lean_ctor_get(v_a_2322_, 6);
v_tags_x3f_2341_ = lean_ctor_get(v_a_2322_, 7);
v_leanTags_x3f_2342_ = lean_ctor_get(v_a_2322_, 8);
v_relatedInformation_x3f_2343_ = lean_ctor_get(v_a_2322_, 9);
v_data_x3f_2344_ = lean_ctor_get(v_a_2322_, 10);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2346_ = v_a_2322_;
v_isShared_2347_ = v_isSharedCheck_2754_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_data_x3f_2344_);
lean_inc(v_relatedInformation_x3f_2343_);
lean_inc(v_leanTags_x3f_2342_);
lean_inc(v_tags_x3f_2341_);
lean_inc(v_message_2340_);
lean_inc(v_source_x3f_2339_);
lean_inc(v_code_x3f_2338_);
lean_inc(v_isSilent_x3f_2337_);
lean_inc(v_severity_x3f_2336_);
lean_inc(v_fullRange_x3f_2335_);
lean_inc(v_range_2334_);
lean_dec(v_a_2322_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2754_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_10349__overap_2349_; lean_object* v___x_2350_; 
v___x_2348_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_range_2334_);
lean_inc_ref(v___x_2333_);
v___x_10349__overap_2349_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2348_);
lean_inc_ref(v_a_2312_);
v___x_2350_ = lean_apply_1(v___x_10349__overap_2349_, v_a_2312_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec(v_source_x3f_2339_);
lean_dec(v_code_x3f_2338_);
lean_dec(v_isSilent_x3f_2337_);
lean_dec(v_severity_x3f_2336_);
lean_dec(v_fullRange_x3f_2335_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2753_; 
v_a_2359_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2361_ = v___x_2350_;
v_isShared_2362_ = v_isSharedCheck_2753_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2350_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2753_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v_____do__lift_2373_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v_____do__lift_2389_; lean_object* v___y_2390_; lean_object* v___f_2413_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v_____do__lift_2422_; lean_object* v___y_2423_; lean_object* v___f_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_____do__lift_2465_; lean_object* v___y_2466_; lean_object* v___f_2500_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v_____do__lift_2506_; lean_object* v___y_2507_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v_____do__lift_2557_; lean_object* v___y_2558_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_j_2601_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_____do__lift_2614_; lean_object* v___y_2615_; lean_object* v___y_2654_; lean_object* v_____do__lift_2655_; lean_object* v___y_2656_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v_____do__lift_2706_; lean_object* v___y_2707_; 
lean_inc_ref_n(v___x_2333_, 3);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2413_, 0, v___x_2327_);
lean_closure_set(v___f_2413_, 1, v___x_2333_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2457_, 0, v___x_2327_);
lean_closure_set(v___f_2457_, 1, v___x_2333_);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2500_, 0, v___x_2327_);
lean_closure_set(v___f_2500_, 1, v___x_2333_);
if (lean_obj_tag(v_fullRange_x3f_2335_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_box(0);
v_____do__lift_2706_ = v___x_2732_;
v___y_2707_ = v_a_2312_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2752_; 
v_val_2733_ = lean_ctor_get(v_fullRange_x3f_2335_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_fullRange_x3f_2335_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2735_ = v_fullRange_x3f_2335_;
v_isShared_2736_ = v_isSharedCheck_2752_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_val_2733_);
lean_dec(v_fullRange_x3f_2335_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2752_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_10402__overap_2738_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_2733_);
lean_inc_ref(v___x_2333_);
v___x_10402__overap_2738_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2737_);
lean_inc_ref(v_a_2312_);
v___x_2739_ = lean_apply_1(v___x_10402__overap_2738_, v_a_2312_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_del_object(v___x_2735_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec(v_source_x3f_2339_);
lean_dec(v_code_x3f_2338_);
lean_dec(v_isSilent_x3f_2337_);
lean_dec(v_severity_x3f_2336_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2739_, 1);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_a_2748_);
v___x_2750_ = v___x_2735_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
v_____do__lift_2706_ = v___x_2750_;
v___y_2707_ = v_a_2312_;
goto v___jp_2705_;
}
}
}
}
v___jp_2363_:
{
lean_object* v___x_2375_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 10, v_____do__lift_2373_);
lean_ctor_set(v___x_2346_, 9, v___y_2369_);
lean_ctor_set(v___x_2346_, 8, v___y_2364_);
lean_ctor_set(v___x_2346_, 7, v___y_2365_);
lean_ctor_set(v___x_2346_, 6, v___y_2367_);
lean_ctor_set(v___x_2346_, 5, v___y_2366_);
lean_ctor_set(v___x_2346_, 4, v___y_2371_);
lean_ctor_set(v___x_2346_, 3, v___y_2370_);
lean_ctor_set(v___x_2346_, 2, v___y_2368_);
lean_ctor_set(v___x_2346_, 1, v___y_2372_);
lean_ctor_set(v___x_2346_, 0, v_a_2359_);
v___x_2375_ = v___x_2346_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___y_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v___y_2368_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v___y_2370_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v___y_2371_);
lean_ctor_set(v_reuseFailAlloc_2379_, 5, v___y_2366_);
lean_ctor_set(v_reuseFailAlloc_2379_, 6, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 7, v___y_2365_);
lean_ctor_set(v_reuseFailAlloc_2379_, 8, v___y_2364_);
lean_ctor_set(v_reuseFailAlloc_2379_, 9, v___y_2369_);
lean_ctor_set(v_reuseFailAlloc_2379_, 10, v_____do__lift_2373_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2375_);
v___x_2377_ = v___x_2361_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
v___jp_2380_:
{
if (lean_obj_tag(v_data_x3f_2344_) == 0)
{
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v___y_2364_ = v___y_2381_;
v___y_2365_ = v___y_2382_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___y_2385_;
v___y_2368_ = v___y_2384_;
v___y_2369_ = v_____do__lift_2389_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2388_;
v_____do__lift_2373_ = v_data_x3f_2344_;
goto v___jp_2363_;
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2412_; 
v_val_2391_ = lean_ctor_get(v_data_x3f_2344_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_data_x3f_2344_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2393_ = v_data_x3f_2344_;
v_isShared_2394_ = v_isSharedCheck_2412_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_data_x3f_2344_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2412_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_val_2391_);
v___x_2396_ = v___x_2324_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_val_2391_);
v___x_2396_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_10351__overap_2397_; lean_object* v___x_2398_; 
v___x_10351__overap_2397_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2396_);
lean_inc_ref(v___y_2390_);
v___x_2398_ = lean_apply_1(v___x_10351__overap_2397_, v___y_2390_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_del_object(v___x_2393_);
lean_dec(v_____do__lift_2389_);
lean_dec(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; 
v_a_2407_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2398_, 1);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_a_2407_);
v___x_2409_ = v___x_2393_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
v___y_2364_ = v___y_2381_;
v___y_2365_ = v___y_2382_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___y_2385_;
v___y_2368_ = v___y_2384_;
v___y_2369_ = v_____do__lift_2389_;
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2388_;
v_____do__lift_2373_ = v___x_2409_;
goto v___jp_2363_;
}
}
}
}
}
}
v___jp_2414_:
{
if (lean_obj_tag(v_relatedInformation_x3f_2343_) == 0)
{
lean_object* v___x_2424_; 
lean_dec_ref(v___f_2413_);
v___x_2424_ = lean_box(0);
v___y_2381_ = v_____do__lift_2422_;
v___y_2382_ = v___y_2415_;
v___y_2383_ = v___y_2416_;
v___y_2384_ = v___y_2418_;
v___y_2385_ = v___y_2417_;
v___y_2386_ = v___y_2419_;
v___y_2387_ = v___y_2420_;
v___y_2388_ = v___y_2421_;
v_____do__lift_2389_ = v___x_2424_;
v___y_2390_ = v___y_2423_;
goto v___jp_2380_;
}
else
{
lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2456_; 
v_val_2425_ = lean_ctor_get(v_relatedInformation_x3f_2343_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_relatedInformation_x3f_2343_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2427_ = v_relatedInformation_x3f_2343_;
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v_relatedInformation_x3f_2343_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___f_2429_; lean_object* v___x_2430_; 
v___f_2429_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2430_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2429_, v_val_2425_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2427_);
lean_dec(v_____do__lift_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
lean_object* v_a_2439_; size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_10103__overap_2442_; lean_object* v___x_2443_; 
v_a_2439_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2430_, 1);
v_sz_2440_ = lean_array_size(v_a_2439_);
v___x_2441_ = ((size_t)0ULL);
v___x_10103__overap_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2327_, v___f_2413_, v_sz_2440_, v___x_2441_, v_a_2439_);
lean_inc_ref(v___y_2423_);
v___x_2443_ = lean_apply_1(v___x_10103__overap_2442_, v___y_2423_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_del_object(v___x_2427_);
lean_dec(v_____do__lift_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; 
v_a_2452_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2443_, 1);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_a_2452_);
v___x_2454_ = v___x_2427_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
v___y_2381_ = v_____do__lift_2422_;
v___y_2382_ = v___y_2415_;
v___y_2383_ = v___y_2416_;
v___y_2384_ = v___y_2418_;
v___y_2385_ = v___y_2417_;
v___y_2386_ = v___y_2419_;
v___y_2387_ = v___y_2420_;
v___y_2388_ = v___y_2421_;
v_____do__lift_2389_ = v___x_2454_;
v___y_2390_ = v___y_2423_;
goto v___jp_2380_;
}
}
}
}
}
}
v___jp_2458_:
{
if (lean_obj_tag(v_leanTags_x3f_2342_) == 0)
{
lean_object* v___x_2467_; 
lean_dec_ref(v___f_2457_);
v___x_2467_ = lean_box(0);
v___y_2415_ = v_____do__lift_2465_;
v___y_2416_ = v___y_2459_;
v___y_2417_ = v___y_2461_;
v___y_2418_ = v___y_2460_;
v___y_2419_ = v___y_2462_;
v___y_2420_ = v___y_2463_;
v___y_2421_ = v___y_2464_;
v_____do__lift_2422_ = v___x_2467_;
v___y_2423_ = v___y_2466_;
goto v___jp_2414_;
}
else
{
lean_object* v_val_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2499_; 
v_val_2468_ = lean_ctor_get(v_leanTags_x3f_2342_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_leanTags_x3f_2342_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2470_ = v_leanTags_x3f_2342_;
v_isShared_2471_ = v_isSharedCheck_2499_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_val_2468_);
lean_dec(v_leanTags_x3f_2342_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2499_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___f_2472_; lean_object* v___x_2473_; 
v___f_2472_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2473_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2472_, v_val_2468_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_del_object(v___x_2470_);
lean_dec(v_____do__lift_2465_);
lean_dec(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_10154__overap_2485_; lean_object* v___x_2486_; 
v_a_2482_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2473_, 1);
v_sz_2483_ = lean_array_size(v_a_2482_);
v___x_2484_ = ((size_t)0ULL);
v___x_10154__overap_2485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2327_, v___f_2457_, v_sz_2483_, v___x_2484_, v_a_2482_);
lean_inc_ref(v___y_2466_);
v___x_2486_ = lean_apply_1(v___x_10154__overap_2485_, v___y_2466_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_del_object(v___x_2470_);
lean_dec(v_____do__lift_2465_);
lean_dec(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2486_, 1);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v_a_2495_);
v___x_2497_ = v___x_2470_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
v___y_2415_ = v_____do__lift_2465_;
v___y_2416_ = v___y_2459_;
v___y_2417_ = v___y_2461_;
v___y_2418_ = v___y_2460_;
v___y_2419_ = v___y_2462_;
v___y_2420_ = v___y_2463_;
v___y_2421_ = v___y_2464_;
v_____do__lift_2422_ = v___x_2497_;
v___y_2423_ = v___y_2466_;
goto v___jp_2414_;
}
}
}
}
}
}
v___jp_2501_:
{
lean_object* v_rpcDecode_2508_; lean_object* v___x_2509_; 
v_rpcDecode_2508_ = lean_ctor_get(v_inst_2310_, 1);
lean_inc_ref(v_rpcDecode_2508_);
lean_dec_ref(v_inst_2310_);
lean_inc_ref(v___y_2507_);
v___x_2509_ = lean_apply_2(v_rpcDecode_2508_, v_message_2340_, v___y_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v_____do__lift_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
if (lean_obj_tag(v_tags_x3f_2341_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v___f_2500_);
v_a_2518_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2509_, 1);
v___x_2519_ = lean_box(0);
v___y_2459_ = v_____do__lift_2506_;
v___y_2460_ = v___y_2502_;
v___y_2461_ = v_a_2518_;
v___y_2462_ = v___y_2503_;
v___y_2463_ = v___y_2504_;
v___y_2464_ = v___y_2505_;
v_____do__lift_2465_ = v___x_2519_;
v___y_2466_ = v___y_2507_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2520_; lean_object* v_val_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2552_; 
v_a_2520_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2509_, 1);
v_val_2521_ = lean_ctor_get(v_tags_x3f_2341_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_tags_x3f_2341_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2523_ = v_tags_x3f_2341_;
v_isShared_2524_ = v_isSharedCheck_2552_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_val_2521_);
lean_dec(v_tags_x3f_2341_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2552_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___f_2525_; lean_object* v___x_2526_; 
v___f_2525_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2526_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2525_, v_val_2521_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_del_object(v___x_2523_);
lean_dec(v_a_2520_);
lean_dec(v_____do__lift_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_a_2535_; size_t v_sz_2536_; size_t v___x_2537_; lean_object* v___x_10205__overap_2538_; lean_object* v___x_2539_; 
v_a_2535_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2526_, 1);
v_sz_2536_ = lean_array_size(v_a_2535_);
v___x_2537_ = ((size_t)0ULL);
v___x_10205__overap_2538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2327_, v___f_2500_, v_sz_2536_, v___x_2537_, v_a_2535_);
lean_inc_ref(v___y_2507_);
v___x_2539_ = lean_apply_1(v___x_10205__overap_2538_, v___y_2507_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2523_);
lean_dec(v_a_2520_);
lean_dec(v_____do__lift_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; 
v_a_2548_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2539_, 1);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v_a_2548_);
v___x_2550_ = v___x_2523_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
v___y_2459_ = v_____do__lift_2506_;
v___y_2460_ = v___y_2502_;
v___y_2461_ = v_a_2520_;
v___y_2462_ = v___y_2503_;
v___y_2463_ = v___y_2504_;
v___y_2464_ = v___y_2505_;
v_____do__lift_2465_ = v___x_2550_;
v___y_2466_ = v___y_2507_;
goto v___jp_2458_;
}
}
}
}
}
}
}
v___jp_2553_:
{
if (lean_obj_tag(v_source_x3f_2339_) == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_box(0);
v___y_2502_ = v___y_2554_;
v___y_2503_ = v___y_2555_;
v___y_2504_ = v_____do__lift_2557_;
v___y_2505_ = v___y_2556_;
v_____do__lift_2506_ = v___x_2559_;
v___y_2507_ = v___y_2558_;
goto v___jp_2501_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2579_; 
v_val_2560_ = lean_ctor_get(v_source_x3f_2339_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_source_x3f_2339_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2562_ = v_source_x3f_2339_;
v_isShared_2563_ = v_isSharedCheck_2579_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_val_2560_);
lean_dec(v_source_x3f_2339_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2579_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_10377__overap_2565_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_Json_getStr_x3f(v_val_2560_);
lean_inc_ref(v___x_2333_);
v___x_10377__overap_2565_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2564_);
lean_inc_ref(v___y_2558_);
v___x_2566_ = lean_apply_1(v___x_10377__overap_2565_, v___y_2558_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_del_object(v___x_2562_);
lean_dec(v_____do__lift_2557_);
lean_dec(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; 
v_a_2575_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2566_, 1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_a_2575_);
v___x_2577_ = v___x_2562_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
v___y_2502_ = v___y_2554_;
v___y_2503_ = v___y_2555_;
v___y_2504_ = v_____do__lift_2557_;
v___y_2505_ = v___y_2556_;
v_____do__lift_2506_ = v___x_2577_;
v___y_2507_ = v___y_2558_;
goto v___jp_2501_;
}
}
}
}
}
v___jp_2580_:
{
if (lean_obj_tag(v___y_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___y_2584_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec(v_source_x3f_2339_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2586_ = lean_ctor_get(v___y_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___y_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___y_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___y_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___y_2585_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___y_2585_, 1);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_a_2594_);
v___y_2554_ = v___y_2581_;
v___y_2555_ = v___y_2582_;
v___y_2556_ = v___y_2584_;
v_____do__lift_2557_ = v___x_2595_;
v___y_2558_ = v___y_2583_;
goto v___jp_2553_;
}
}
v___jp_2596_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_10379__overap_2609_; lean_object* v___x_2610_; 
v___x_2602_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2603_ = lean_unsigned_to_nat(80u);
v___x_2604_ = l_Lean_Json_pretty(v_j_2601_, v___x_2603_);
v___x_2605_ = lean_string_append(v___x_2602_, v___x_2604_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2607_ = lean_string_append(v___x_2605_, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_inc_ref(v___x_2333_);
v___x_10379__overap_2609_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2608_);
lean_inc_ref(v___y_2599_);
v___x_2610_ = lean_apply_1(v___x_10379__overap_2609_, v___y_2599_);
v___y_2581_ = v___y_2597_;
v___y_2582_ = v___y_2598_;
v___y_2583_ = v___y_2599_;
v___y_2584_ = v___y_2600_;
v___y_2585_ = v___x_2610_;
goto v___jp_2580_;
}
v___jp_2611_:
{
if (lean_obj_tag(v_code_x3f_2338_) == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_box(0);
v___y_2554_ = v___y_2612_;
v___y_2555_ = v_____do__lift_2614_;
v___y_2556_ = v___y_2613_;
v_____do__lift_2557_ = v___x_2616_;
v___y_2558_ = v___y_2615_;
goto v___jp_2553_;
}
else
{
lean_object* v_val_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2652_; 
v_val_2617_ = lean_ctor_get(v_code_x3f_2338_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_code_x3f_2338_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2619_ = v_code_x3f_2338_;
v_isShared_2620_ = v_isSharedCheck_2652_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_val_2617_);
lean_dec(v_code_x3f_2338_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2652_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
switch(lean_obj_tag(v_val_2617_))
{
case 2:
{
lean_object* v_n_2621_; lean_object* v_mantissa_2622_; lean_object* v_exponent_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_n_2621_ = lean_ctor_get(v_val_2617_, 0);
v_mantissa_2622_ = lean_ctor_get(v_n_2621_, 0);
v_exponent_2623_ = lean_ctor_get(v_n_2621_, 1);
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_nat_dec_eq(v_exponent_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_del_object(v___x_2619_);
v___y_2597_ = v___y_2612_;
v___y_2598_ = v_____do__lift_2614_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2613_;
v_j_2601_ = v_val_2617_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2637_; 
lean_inc(v_mantissa_2622_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_val_2617_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v_val_2617_, 0);
lean_dec(v_unused_2638_);
v___x_2627_ = v_val_2617_;
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v_val_2617_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set_tag(v___x_2627_, 0);
lean_ctor_set(v___x_2627_, 0, v_mantissa_2622_);
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_mantissa_2622_);
v___x_2630_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2630_);
v___x_2632_ = v___x_2619_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_10382__overap_2633_; lean_object* v___x_2634_; 
lean_inc_ref(v___x_2333_);
v___x_10382__overap_2633_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2632_);
lean_inc_ref(v___y_2615_);
v___x_2634_ = lean_apply_1(v___x_10382__overap_2633_, v___y_2615_);
v___y_2581_ = v___y_2612_;
v___y_2582_ = v_____do__lift_2614_;
v___y_2583_ = v___y_2615_;
v___y_2584_ = v___y_2613_;
v___y_2585_ = v___x_2634_;
goto v___jp_2580_;
}
}
}
}
}
case 3:
{
lean_object* v_s_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2651_; 
v_s_2639_ = lean_ctor_get(v_val_2617_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_val_2617_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2641_ = v_val_2617_;
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_s_2639_);
lean_dec(v_val_2617_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_s_2639_);
v___x_2644_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2644_);
v___x_2646_ = v___x_2619_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_10384__overap_2647_; lean_object* v___x_2648_; 
lean_inc_ref(v___x_2333_);
v___x_10384__overap_2647_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2646_);
lean_inc_ref(v___y_2615_);
v___x_2648_ = lean_apply_1(v___x_10384__overap_2647_, v___y_2615_);
v___y_2581_ = v___y_2612_;
v___y_2582_ = v_____do__lift_2614_;
v___y_2583_ = v___y_2615_;
v___y_2584_ = v___y_2613_;
v___y_2585_ = v___x_2648_;
goto v___jp_2580_;
}
}
}
}
default: 
{
lean_del_object(v___x_2619_);
v___y_2597_ = v___y_2612_;
v___y_2598_ = v_____do__lift_2614_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2613_;
v_j_2601_ = v_val_2617_;
goto v___jp_2596_;
}
}
}
}
}
v___jp_2653_:
{
if (lean_obj_tag(v_isSilent_x3f_2337_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_box(0);
v___y_2612_ = v_____do__lift_2655_;
v___y_2613_ = v___y_2654_;
v_____do__lift_2614_ = v___x_2657_;
v___y_2615_ = v___y_2656_;
goto v___jp_2611_;
}
else
{
lean_object* v_val_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2677_; 
v_val_2658_ = lean_ctor_get(v_isSilent_x3f_2337_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_isSilent_x3f_2337_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2660_ = v_isSilent_x3f_2337_;
v_isShared_2661_ = v_isSharedCheck_2677_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_val_2658_);
lean_dec(v_isSilent_x3f_2337_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2677_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_10386__overap_2663_; lean_object* v___x_2664_; 
v___x_2662_ = l_Lean_Json_getBool_x3f(v_val_2658_);
lean_dec(v_val_2658_);
lean_inc_ref(v___x_2333_);
v___x_10386__overap_2663_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2662_);
lean_inc_ref(v___y_2656_);
v___x_2664_ = lean_apply_1(v___x_10386__overap_2663_, v___y_2656_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_del_object(v___x_2660_);
lean_dec(v_____do__lift_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec(v_source_x3f_2339_);
lean_dec(v_code_x3f_2338_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2664_, 1);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v_a_2673_);
v___x_2675_ = v___x_2660_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v___y_2612_ = v_____do__lift_2655_;
v___y_2613_ = v___y_2654_;
v_____do__lift_2614_ = v___x_2675_;
v___y_2615_ = v___y_2656_;
goto v___jp_2611_;
}
}
}
}
}
v___jp_2678_:
{
if (lean_obj_tag(v___y_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v___y_2680_);
lean_dec_ref(v___f_2500_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2413_);
lean_del_object(v___x_2361_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2346_);
lean_dec(v_data_x3f_2344_);
lean_dec(v_relatedInformation_x3f_2343_);
lean_dec(v_leanTags_x3f_2342_);
lean_dec(v_tags_x3f_2341_);
lean_dec(v_message_2340_);
lean_dec(v_source_x3f_2339_);
lean_dec(v_code_x3f_2338_);
lean_dec(v_isSilent_x3f_2337_);
lean_dec_ref(v___x_2333_);
lean_del_object(v___x_2324_);
lean_dec_ref(v_inst_2310_);
v_a_2682_ = lean_ctor_get(v___y_2681_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___y_2681_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___y_2681_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___y_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___y_2681_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___y_2681_, 1);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_a_2690_);
v___y_2654_ = v___y_2680_;
v_____do__lift_2655_ = v___x_2691_;
v___y_2656_ = v___y_2679_;
goto v___jp_2653_;
}
}
v___jp_2692_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_10388__overap_2703_; lean_object* v___x_2704_; 
v___x_2696_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2697_ = lean_unsigned_to_nat(80u);
v___x_2698_ = l_Lean_Json_pretty(v___y_2694_, v___x_2697_);
v___x_2699_ = lean_string_append(v___x_2696_, v___x_2698_);
lean_dec_ref(v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_inc_ref(v___x_2333_);
v___x_10388__overap_2703_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2702_);
lean_inc_ref(v___y_2693_);
v___x_2704_ = lean_apply_1(v___x_10388__overap_2703_, v___y_2693_);
v___y_2679_ = v___y_2693_;
v___y_2680_ = v___y_2695_;
v___y_2681_ = v___x_2704_;
goto v___jp_2678_;
}
v___jp_2705_:
{
if (lean_obj_tag(v_severity_x3f_2336_) == 0)
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_box(0);
v___y_2654_ = v_____do__lift_2706_;
v_____do__lift_2655_ = v___x_2708_;
v___y_2656_ = v___y_2707_;
goto v___jp_2653_;
}
else
{
lean_object* v_val_2709_; lean_object* v___x_2710_; 
v_val_2709_ = lean_ctor_get(v_severity_x3f_2336_, 0);
lean_inc_n(v_val_2709_, 2);
lean_dec_ref_known(v_severity_x3f_2336_, 1);
v___x_2710_ = l_Lean_Json_getNat_x3f(v_val_2709_);
if (lean_obj_tag(v___x_2710_) == 1)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = lean_nat_dec_eq(v_a_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = lean_unsigned_to_nat(2u);
v___x_2715_ = lean_nat_dec_eq(v_a_2711_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = lean_unsigned_to_nat(3u);
v___x_2717_ = lean_nat_dec_eq(v_a_2711_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = lean_unsigned_to_nat(4u);
v___x_2719_ = lean_nat_dec_eq(v_a_2711_, v___x_2718_);
lean_dec(v_a_2711_);
if (v___x_2719_ == 0)
{
v___y_2693_ = v___y_2707_;
v___y_2694_ = v_val_2709_;
v___y_2695_ = v_____do__lift_2706_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_10394__overap_2721_; lean_object* v___x_2722_; 
lean_dec(v_val_2709_);
v___x_2720_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2333_);
v___x_10394__overap_2721_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2720_);
lean_inc_ref(v___y_2707_);
v___x_2722_ = lean_apply_1(v___x_10394__overap_2721_, v___y_2707_);
v___y_2679_ = v___y_2707_;
v___y_2680_ = v_____do__lift_2706_;
v___y_2681_ = v___x_2722_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2723_; lean_object* v___x_10396__overap_2724_; lean_object* v___x_2725_; 
lean_dec(v_a_2711_);
lean_dec(v_val_2709_);
v___x_2723_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2333_);
v___x_10396__overap_2724_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2723_);
lean_inc_ref(v___y_2707_);
v___x_2725_ = lean_apply_1(v___x_10396__overap_2724_, v___y_2707_);
v___y_2679_ = v___y_2707_;
v___y_2680_ = v_____do__lift_2706_;
v___y_2681_ = v___x_2725_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_10398__overap_2727_; lean_object* v___x_2728_; 
lean_dec(v_a_2711_);
lean_dec(v_val_2709_);
v___x_2726_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2333_);
v___x_10398__overap_2727_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2726_);
lean_inc_ref(v___y_2707_);
v___x_2728_ = lean_apply_1(v___x_10398__overap_2727_, v___y_2707_);
v___y_2679_ = v___y_2707_;
v___y_2680_ = v_____do__lift_2706_;
v___y_2681_ = v___x_2728_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_10400__overap_2730_; lean_object* v___x_2731_; 
lean_dec(v_a_2711_);
lean_dec(v_val_2709_);
v___x_2729_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2333_);
v___x_10400__overap_2730_ = l_MonadExcept_ofExcept___redArg(v___x_2327_, v___x_2333_, v___x_2729_);
lean_inc_ref(v___y_2707_);
v___x_2731_ = lean_apply_1(v___x_10400__overap_2730_, v___y_2707_);
v___y_2679_ = v___y_2707_;
v___y_2680_ = v_____do__lift_2706_;
v___y_2681_ = v___x_2731_;
goto v___jp_2678_;
}
}
else
{
lean_dec_ref(v___x_2710_);
v___y_2693_ = v___y_2707_;
v___y_2694_ = v_val_2709_;
v___y_2695_ = v_____do__lift_2706_;
goto v___jp_2692_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_inst_2756_, lean_object* v_j_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2756_, v_j_2757_, v_a_2758_);
lean_dec_ref(v_a_2758_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2760_, lean_object* v_inst_2761_, lean_object* v_j_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2761_, v_j_2762_, v_a_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_00_u03b1_2765_, lean_object* v_inst_2766_, lean_object* v_j_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_00_u03b1_2765_, v_inst_2766_, v_j_2767_, v_a_2768_);
lean_dec_ref(v_a_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object* v_inst_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_inc_ref(v_inst_2770_);
v___x_2771_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___x_2771_, 0, lean_box(0));
lean_closure_set(v___x_2771_, 1, v_inst_2770_);
v___x_2772_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___x_2772_, 0, lean_box(0));
lean_closure_set(v___x_2772_, 1, v_inst_2770_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object* v_00_u03b1_2774_, lean_object* v_inst_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(v_inst_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object* v_x_2780_, lean_object* v_x_2781_){
_start:
{
switch(lean_obj_tag(v_x_2780_))
{
case 0:
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
v_a_2782_ = lean_ctor_get(v_x_2780_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2780_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2784_ = v_x_2780_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v_x_2780_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_a_2782_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
case 1:
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2802_; 
v_a_2791_ = lean_ctor_get(v_x_2780_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_x_2780_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2793_ = v_x_2780_;
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v_x_2780_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2795_ = l_Lean_Widget_InteractiveGoal_pretty(v_a_2791_);
v___x_2796_ = l_Std_Format_defWidth;
v___x_2797_ = lean_unsigned_to_nat(0u);
v___x_2798_ = l_Std_Format_pretty(v___x_2795_, v___x_2796_, v___x_2797_, v___x_2797_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2798_);
v___x_2800_ = v___x_2793_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
case 2:
{
lean_object* v_alt_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_alt_2803_ = lean_ctor_get(v_x_2780_, 1);
lean_inc_ref(v_alt_2803_);
lean_dec_ref_known(v_x_2780_, 2);
v___x_2804_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_alt_2803_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
default: 
{
lean_object* v___x_2806_; 
lean_dec_ref_known(v_x_2780_, 4);
v___x_2806_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1));
return v___x_2806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(v_x_2807_, v_x_2808_);
lean_dec_ref(v_x_2808_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object* v_tt_2810_){
_start:
{
lean_object* v___f_2811_; lean_object* v_tt_2812_; lean_object* v___x_2813_; 
v___f_2811_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed), 2, 0);
v_tt_2812_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_2811_, v_tt_2810_);
v___x_2813_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object* v_diag_2814_){
_start:
{
lean_object* v_range_2815_; lean_object* v_fullRange_x3f_2816_; lean_object* v_severity_x3f_2817_; lean_object* v_isSilent_x3f_2818_; lean_object* v_code_x3f_2819_; lean_object* v_source_x3f_2820_; lean_object* v_message_2821_; lean_object* v_tags_x3f_2822_; lean_object* v_leanTags_x3f_2823_; lean_object* v_relatedInformation_x3f_2824_; lean_object* v_data_x3f_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2833_; 
v_range_2815_ = lean_ctor_get(v_diag_2814_, 0);
v_fullRange_x3f_2816_ = lean_ctor_get(v_diag_2814_, 1);
v_severity_x3f_2817_ = lean_ctor_get(v_diag_2814_, 2);
v_isSilent_x3f_2818_ = lean_ctor_get(v_diag_2814_, 3);
v_code_x3f_2819_ = lean_ctor_get(v_diag_2814_, 4);
v_source_x3f_2820_ = lean_ctor_get(v_diag_2814_, 5);
v_message_2821_ = lean_ctor_get(v_diag_2814_, 6);
v_tags_x3f_2822_ = lean_ctor_get(v_diag_2814_, 7);
v_leanTags_x3f_2823_ = lean_ctor_get(v_diag_2814_, 8);
v_relatedInformation_x3f_2824_ = lean_ctor_get(v_diag_2814_, 9);
v_data_x3f_2825_ = lean_ctor_get(v_diag_2814_, 10);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_diag_2814_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2827_ = v_diag_2814_;
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_data_x3f_2825_);
lean_inc(v_relatedInformation_x3f_2824_);
lean_inc(v_leanTags_x3f_2823_);
lean_inc(v_tags_x3f_2822_);
lean_inc(v_message_2821_);
lean_inc(v_source_x3f_2820_);
lean_inc(v_code_x3f_2819_);
lean_inc(v_isSilent_x3f_2818_);
lean_inc(v_severity_x3f_2817_);
lean_inc(v_fullRange_x3f_2816_);
lean_inc(v_range_2815_);
lean_dec(v_diag_2814_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2829_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_message_2821_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 6, v___x_2829_);
v___x_2831_ = v___x_2827_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_range_2815_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_fullRange_x3f_2816_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_severity_x3f_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_isSilent_x3f_2818_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_code_x3f_2819_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v_source_x3f_2820_);
lean_ctor_set(v_reuseFailAlloc_2832_, 6, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2832_, 7, v_tags_x3f_2822_);
lean_ctor_set(v_reuseFailAlloc_2832_, 8, v_leanTags_x3f_2823_);
lean_ctor_set(v_reuseFailAlloc_2832_, 9, v_relatedInformation_x3f_2824_);
lean_ctor_set(v_reuseFailAlloc_2832_, 10, v_data_x3f_2825_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object* v_nCtx_2834_, lean_object* v_ctx_2835_){
_start:
{
lean_object* v_env_2836_; lean_object* v_mctx_2837_; lean_object* v_lctx_2838_; lean_object* v_opts_2839_; lean_object* v_currNamespace_2840_; lean_object* v_openDecls_2841_; lean_object* v___x_2842_; 
v_env_2836_ = lean_ctor_get(v_ctx_2835_, 0);
v_mctx_2837_ = lean_ctor_get(v_ctx_2835_, 1);
v_lctx_2838_ = lean_ctor_get(v_ctx_2835_, 2);
v_opts_2839_ = lean_ctor_get(v_ctx_2835_, 3);
v_currNamespace_2840_ = lean_ctor_get(v_nCtx_2834_, 0);
v_openDecls_2841_ = lean_ctor_get(v_nCtx_2834_, 1);
lean_inc(v_openDecls_2841_);
lean_inc(v_currNamespace_2840_);
lean_inc_ref(v_opts_2839_);
lean_inc_ref(v_lctx_2838_);
lean_inc_ref(v_mctx_2837_);
lean_inc_ref(v_env_2836_);
v___x_2842_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2842_, 0, v_env_2836_);
lean_ctor_set(v___x_2842_, 1, v_mctx_2837_);
lean_ctor_set(v___x_2842_, 2, v_lctx_2838_);
lean_ctor_set(v___x_2842_, 3, v_opts_2839_);
lean_ctor_set(v___x_2842_, 4, v_currNamespace_2840_);
lean_ctor_set(v___x_2842_, 5, v_openDecls_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object* v_nCtx_2843_, lean_object* v_ctx_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_2843_, v_ctx_2844_);
lean_dec_ref(v_ctx_2844_);
lean_dec_ref(v_nCtx_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl(lean_object* v_x_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_obj_tag_nat(v_x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl___boxed(lean_object* v_x_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl(v_x_2848_);
lean_dec(v_x_2848_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(lean_object* v_t_2850_, lean_object* v_k_2851_){
_start:
{
switch(lean_obj_tag(v_t_2850_))
{
case 1:
{
lean_object* v_ctx_2852_; lean_object* v_lctx_2853_; lean_object* v_g_2854_; lean_object* v___x_2855_; 
v_ctx_2852_ = lean_ctor_get(v_t_2850_, 0);
lean_inc_ref(v_ctx_2852_);
v_lctx_2853_ = lean_ctor_get(v_t_2850_, 1);
lean_inc_ref(v_lctx_2853_);
v_g_2854_ = lean_ctor_get(v_t_2850_, 2);
lean_inc(v_g_2854_);
lean_dec_ref_known(v_t_2850_, 3);
v___x_2855_ = lean_apply_3(v_k_2851_, v_ctx_2852_, v_lctx_2853_, v_g_2854_);
return v___x_2855_;
}
case 3:
{
lean_object* v_cls_2856_; lean_object* v_msg_2857_; uint8_t v_collapsed_2858_; lean_object* v_children_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_cls_2856_ = lean_ctor_get(v_t_2850_, 0);
lean_inc(v_cls_2856_);
v_msg_2857_ = lean_ctor_get(v_t_2850_, 1);
lean_inc(v_msg_2857_);
v_collapsed_2858_ = lean_ctor_get_uint8(v_t_2850_, sizeof(void*)*3);
v_children_2859_ = lean_ctor_get(v_t_2850_, 2);
lean_inc_ref(v_children_2859_);
lean_dec_ref_known(v_t_2850_, 3);
v___x_2860_ = lean_box(v_collapsed_2858_);
v___x_2861_ = lean_apply_4(v_k_2851_, v_cls_2856_, v_msg_2857_, v___x_2860_, v_children_2859_);
return v___x_2861_;
}
case 4:
{
return v_k_2851_;
}
default: 
{
lean_object* v_ctx_2862_; lean_object* v_infos_2863_; lean_object* v___x_2864_; 
v_ctx_2862_ = lean_ctor_get(v_t_2850_, 0);
lean_inc_ref(v_ctx_2862_);
v_infos_2863_ = lean_ctor_get(v_t_2850_, 1);
lean_inc(v_infos_2863_);
lean_dec(v_t_2850_);
v___x_2864_ = lean_apply_2(v_k_2851_, v_ctx_2862_, v_infos_2863_);
return v___x_2864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(lean_object* v_motive_2865_, lean_object* v_ctorIdx_2866_, lean_object* v_t_2867_, lean_object* v_h_2868_, lean_object* v_k_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2867_, v_k_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___boxed(lean_object* v_motive_2871_, lean_object* v_ctorIdx_2872_, lean_object* v_t_2873_, lean_object* v_h_2874_, lean_object* v_k_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(v_motive_2871_, v_ctorIdx_2872_, v_t_2873_, v_h_2874_, v_k_2875_);
lean_dec(v_ctorIdx_2872_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim___redArg(lean_object* v_t_2877_, lean_object* v_code_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2877_, v_code_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim(lean_object* v_motive_2880_, lean_object* v_t_2881_, lean_object* v_h_2882_, lean_object* v_code_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2881_, v_code_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim___redArg(lean_object* v_t_2885_, lean_object* v_goal_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2885_, v_goal_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim(lean_object* v_motive_2888_, lean_object* v_t_2889_, lean_object* v_h_2890_, lean_object* v_goal_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2889_, v_goal_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim___redArg(lean_object* v_t_2893_, lean_object* v_widget_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2893_, v_widget_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim(lean_object* v_motive_2896_, lean_object* v_t_2897_, lean_object* v_h_2898_, lean_object* v_widget_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2897_, v_widget_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim___redArg(lean_object* v_t_2901_, lean_object* v_trace_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2901_, v_trace_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim(lean_object* v_motive_2904_, lean_object* v_t_2905_, lean_object* v_h_2906_, lean_object* v_trace_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2905_, v_trace_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim___redArg(lean_object* v_t_2909_, lean_object* v_ignoreTags_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2909_, v_ignoreTags_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim(lean_object* v_motive_2912_, lean_object* v_t_2913_, lean_object* v_h_2914_, lean_object* v_ignoreTags_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2913_, v_ignoreTags_2915_);
return v___x_2916_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0(void){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Array_instInhabited___redArg();
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2(void){
_start:
{
lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2920_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1);
v___x_2921_ = 0;
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_box(0);
v___x_2924_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___x_2922_);
lean_ctor_set(v___x_2924_, 2, v___x_2920_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3, v___x_2921_);
return v___x_2924_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default(void){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2);
return v___x_2925_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt(void){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Widget_instInhabitedEmbedFmt_default;
return v___x_2926_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object* v_e_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = lean_array_get_size(v_a_2928_);
v___x_2931_ = lean_array_push(v_a_2928_, v_e_2927_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2927_ = stack[0].m_obj;
lean_object* v_a_2928_ = stack[1].m_obj;
lean_object* v_res_2934_;
v_res_2934_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v_e_2927_, v_a_2928_);
stack->m_obj
 = v_res_2934_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed___boxed(lean_object* v_e_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v_e_2935_, v_a_2936_);
return v_res_2938_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object* v_fmt_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2961_; 
v___x_2942_ = lean_box(4);
v___x_2943_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_2942_, v_a_2940_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2960_; 
v_fst_2948_ = lean_ctor_get(v_a_2944_, 0);
v_snd_2949_ = lean_ctor_get(v_a_2944_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2951_ = v_a_2944_;
v_isShared_2952_ = v_isSharedCheck_2960_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snd_2949_);
lean_inc(v_fst_2948_);
lean_dec(v_a_2944_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2960_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_fst_2948_);
lean_ctor_set(v___x_2953_, 1, v_fmt_2939_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_snd_2949_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2955_);
v___x_2957_ = v___x_2946_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags_0interp(lean_interpreter_value* stack)
{
lean_object* v_fmt_2939_ = stack[0].m_obj;
lean_object* v_a_2940_ = stack[1].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_2939_, v_a_2940_);
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags___boxed(lean_object* v_fmt_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_2963_, v_a_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object* v_nCtx_2975_, lean_object* v_ctx_2976_){
_start:
{
lean_object* v_env_2977_; lean_object* v_mctx_2978_; lean_object* v_opts_2979_; lean_object* v_currNamespace_2980_; lean_object* v_openDecls_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_env_2977_ = lean_ctor_get(v_ctx_2976_, 0);
v_mctx_2978_ = lean_ctor_get(v_ctx_2976_, 1);
v_opts_2979_ = lean_ctor_get(v_ctx_2976_, 3);
v_currNamespace_2980_ = lean_ctor_get(v_nCtx_2975_, 0);
v_openDecls_2981_ = lean_ctor_get(v_nCtx_2975_, 1);
v___x_2982_ = lean_box(0);
v___x_2983_ = l_Lean_instInhabitedFileMap_default;
v___x_2984_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2));
lean_inc(v_openDecls_2981_);
lean_inc(v_currNamespace_2980_);
lean_inc_ref(v_opts_2979_);
lean_inc_ref(v_mctx_2978_);
lean_inc_ref(v_env_2977_);
v___x_2985_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2985_, 0, v_env_2977_);
lean_ctor_set(v___x_2985_, 1, v___x_2982_);
lean_ctor_set(v___x_2985_, 2, v___x_2983_);
lean_ctor_set(v___x_2985_, 3, v_mctx_2978_);
lean_ctor_set(v___x_2985_, 4, v_opts_2979_);
lean_ctor_set(v___x_2985_, 5, v_currNamespace_2980_);
lean_ctor_set(v___x_2985_, 6, v_openDecls_2981_);
lean_ctor_set(v___x_2985_, 7, v___x_2984_);
v___x_2986_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3));
v___x_2987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2982_);
lean_ctor_set(v___x_2987_, 2, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object* v_nCtx_2988_, lean_object* v_ctx_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_2988_, v_ctx_2989_);
lean_dec_ref(v_ctx_2989_);
lean_dec_ref(v_nCtx_2988_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(lean_object* v_a_2991_, lean_object* v_b_2992_){
_start:
{
lean_object* v_array_2993_; lean_object* v_start_2994_; lean_object* v_stop_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3008_; 
v_array_2993_ = lean_ctor_get(v_a_2991_, 0);
v_start_2994_ = lean_ctor_get(v_a_2991_, 1);
v_stop_2995_ = lean_ctor_get(v_a_2991_, 2);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_a_2991_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2997_ = v_a_2991_;
v_isShared_2998_ = v_isSharedCheck_3008_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_stop_2995_);
lean_inc(v_start_2994_);
lean_inc(v_array_2993_);
lean_dec(v_a_2991_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3008_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_nat_dec_lt(v_start_2994_, v_stop_2995_);
if (v___x_2999_ == 0)
{
lean_del_object(v___x_2997_);
lean_dec(v_stop_2995_);
lean_dec(v_start_2994_);
lean_dec_ref(v_array_2993_);
return v_b_2992_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = lean_nat_add(v_start_2994_, v___x_3000_);
lean_inc_ref(v_array_2993_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v___x_3001_);
v___x_3003_ = v___x_2997_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_array_2993_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_stop_2995_);
v___x_3003_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_array_fget(v_array_2993_, v_start_2994_);
lean_dec(v_start_2994_);
lean_dec_ref(v_array_2993_);
v___x_3005_ = lean_array_push(v_b_2992_, v___x_3004_);
v_a_2991_ = v___x_3003_;
v_b_2992_ = v___x_3005_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1(void){
_start:
{
lean_object* v___x_3011_; double v___x_3012_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_float_of_nat(v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object* v_cls_3017_, lean_object* v_blockSize_3018_, lean_object* v_children_3019_){
_start:
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_nat_dec_lt(v___x_3020_, v_blockSize_3018_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v_cls_3017_);
v___x_3022_ = l_Subarray_copy___redArg(v_children_3019_);
return v___x_3022_;
}
else
{
lean_object* v_start_3023_; lean_object* v_stop_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_start_3023_ = lean_ctor_get(v_children_3019_, 1);
v_stop_3024_ = lean_ctor_get(v_children_3019_, 2);
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_add(v_blockSize_3018_, v___x_3025_);
v___x_3027_ = lean_nat_sub(v_stop_3024_, v_start_3023_);
v___x_3028_ = lean_nat_dec_lt(v___x_3026_, v___x_3027_);
lean_dec(v___x_3026_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
lean_dec(v___x_3027_);
lean_dec(v_cls_3017_);
v___x_3029_ = l_Subarray_copy___redArg(v_children_3019_);
return v___x_3029_;
}
else
{
lean_object* v___x_3030_; lean_object* v_more_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; double v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_inc_ref(v_children_3019_);
v___x_3030_ = l_Subarray_drop___redArg(v_children_3019_, v_blockSize_3018_);
lean_inc(v_cls_3017_);
v_more_3031_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3017_, v_blockSize_3018_, v___x_3030_);
v___x_3032_ = l_Subarray_take___redArg(v_children_3019_, v_blockSize_3018_);
v___x_3033_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0));
v___x_3034_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3037_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2));
v___x_3038_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3038_, 0, v_cls_3017_);
lean_ctor_set(v___x_3038_, 1, v___x_3035_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
lean_ctor_set_float(v___x_3038_, sizeof(void*)*3, v___x_3036_);
lean_ctor_set_float(v___x_3038_, sizeof(void*)*3 + 8, v___x_3036_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*3 + 16, v___x_3021_);
v___x_3039_ = lean_nat_sub(v___x_3027_, v_blockSize_3018_);
lean_dec(v___x_3027_);
v___x_3040_ = l_Nat_reprFast(v___x_3039_);
v___x_3041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4));
v___x_3043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_MessageData_ofFormat(v___x_3043_);
v___x_3045_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3038_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
lean_ctor_set(v___x_3045_, 2, v_more_3031_);
v___x_3046_ = lean_array_push(v___x_3034_, v___x_3045_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object* v_cls_3047_, lean_object* v_blockSize_3048_, lean_object* v_children_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3047_, v_blockSize_3048_, v_children_3049_);
lean_dec(v_blockSize_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0(lean_object* v_inst_3051_, lean_object* v_R_3052_, lean_object* v_a_3053_, lean_object* v_b_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v_a_3053_, v_b_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_nat_to_int(v_a_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object* v_opts_3058_, lean_object* v_opt_3059_){
_start:
{
lean_object* v_name_3060_; lean_object* v_map_3061_; lean_object* v___x_3062_; 
v_name_3060_ = lean_ctor_get(v_opt_3059_, 0);
v_map_3061_ = lean_ctor_get(v_opts_3058_, 0);
v___x_3062_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3061_, v_name_3060_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_box(0);
return v___x_3063_;
}
else
{
lean_object* v_val_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3073_; 
v_val_3064_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3066_ = v___x_3062_;
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_val_3064_);
lean_dec(v___x_3062_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
if (lean_obj_tag(v_val_3064_) == 3)
{
lean_object* v_v_3068_; lean_object* v___x_3070_; 
v_v_3068_ = lean_ctor_get(v_val_3064_, 0);
lean_inc(v_v_3068_);
lean_dec_ref_known(v_val_3064_, 1);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_v_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_v_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
else
{
lean_object* v___x_3072_; 
lean_del_object(v___x_3066_);
lean_dec(v_val_3064_);
v___x_3072_ = lean_box(0);
return v___x_3072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object* v_opts_3074_, lean_object* v_opt_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3074_, v_opt_3075_);
lean_dec_ref(v_opt_3075_);
lean_dec_ref(v_opts_3074_);
return v_res_3076_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object* v_ctx_3077_, lean_object* v_nCtx_3078_, size_t v_sz_3079_, size_t v_i_3080_, lean_object* v_bs_3081_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_lt(v_i_3080_, v_sz_3079_);
if (v___x_3082_ == 0)
{
lean_dec_ref(v_nCtx_3078_);
return v_bs_3081_;
}
else
{
lean_object* v_v_3083_; lean_object* v___x_3084_; lean_object* v_bs_x27_3085_; lean_object* v___y_3087_; 
v_v_3083_ = lean_array_uget(v_bs_3081_, v_i_3080_);
v___x_3084_ = lean_unsigned_to_nat(0u);
v_bs_x27_3085_ = lean_array_uset(v_bs_3081_, v_i_3080_, v___x_3084_);
if (lean_obj_tag(v_ctx_3077_) == 0)
{
lean_object* v___x_3092_; 
lean_inc_ref(v_nCtx_3078_);
v___x_3092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_nCtx_3078_);
lean_ctor_set(v___x_3092_, 1, v_v_3083_);
v___y_3087_ = v___x_3092_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_val_3093_ = lean_ctor_get(v_ctx_3077_, 0);
lean_inc(v_val_3093_);
v___x_3094_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_val_3093_);
lean_ctor_set(v___x_3094_, 1, v_v_3083_);
lean_inc_ref(v_nCtx_3078_);
v___x_3095_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_nCtx_3078_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___y_3087_ = v___x_3095_;
goto v___jp_3086_;
}
v___jp_3086_:
{
size_t v___x_3088_; size_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = ((size_t)1ULL);
v___x_3089_ = lean_usize_add(v_i_3080_, v___x_3088_);
v___x_3090_ = lean_array_uset(v_bs_x27_3085_, v_i_3080_, v___y_3087_);
v_i_3080_ = v___x_3089_;
v_bs_3081_ = v___x_3090_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3077_ = stack[0].m_obj;
lean_object* v_nCtx_3078_ = stack[1].m_obj;
size_t v_sz_3079_ = stack[2].m_num;
size_t v_i_3080_ = stack[3].m_num;
lean_object* v_bs_3081_ = stack[4].m_obj;
lean_object* v_res_3096_;
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v_ctx_3077_, v_nCtx_3078_, v_sz_3079_, v_i_3080_, v_bs_3081_);
stack->m_obj
 = v_res_3096_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object* v_ctx_3097_, lean_object* v_nCtx_3098_, lean_object* v_sz_3099_, lean_object* v_i_3100_, lean_object* v_bs_3101_){
_start:
{
size_t v_sz_boxed_3102_; size_t v_i_boxed_3103_; lean_object* v_res_3104_; 
v_sz_boxed_3102_ = lean_unbox_usize(v_sz_3099_);
lean_dec(v_sz_3099_);
v_i_boxed_3103_ = lean_unbox_usize(v_i_3100_);
lean_dec(v_i_3100_);
v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v_ctx_3097_, v_nCtx_3098_, v_sz_boxed_3102_, v_i_boxed_3103_, v_bs_3101_);
lean_dec(v_ctx_3097_);
return v_res_3104_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_unsigned_to_nat(4u);
v___x_3112_ = lean_nat_to_int(v___x_3111_);
return v___x_3112_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7));
v___x_3118_ = lean_mk_io_user_error(v___x_3117_);
return v___x_3118_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object* v_nCtx_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
uint8_t v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v_nodes_3131_; lean_object* v___y_3132_; uint8_t v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; uint8_t v___y_3204_; uint8_t v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v_header_3226_; lean_object* v___y_3227_; lean_object* v___y_3232_; double v___y_3233_; uint8_t v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; double v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3250_; double v___y_3251_; uint8_t v___y_3252_; uint8_t v___y_3253_; lean_object* v___y_3254_; double v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v_ctx_3262_; lean_object* v_data_3263_; lean_object* v_header_3264_; lean_object* v_children_3265_; lean_object* v___y_3266_; lean_object* v_ctx_3329_; lean_object* v_n_3330_; lean_object* v_d_3331_; lean_object* v___y_3332_; lean_object* v_ctx_3354_; lean_object* v_wi_3355_; lean_object* v_d_3356_; lean_object* v___y_3357_; lean_object* v_ctx_3398_; lean_object* v_d_3399_; lean_object* v___y_3400_; lean_object* v_ctx_3404_; lean_object* v_d_u2081_3405_; lean_object* v_d_u2082_3406_; lean_object* v___y_3407_; lean_object* v_ctx_3438_; lean_object* v_d_3439_; lean_object* v___y_3440_; lean_object* v___x_3461_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; 
v___x_3461_ = l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_;
if (lean_obj_tag(v_a_3123_) == 0)
{
switch(lean_obj_tag(v_a_3124_))
{
case 0:
{
lean_object* v_a_3473_; lean_object* v_fmt_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v_nCtx_3122_);
v_a_3473_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3473_);
lean_dec_ref_known(v_a_3124_, 1);
v_fmt_3474_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_fmt_3474_);
lean_dec_ref(v_a_3473_);
v___x_3475_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_3474_, v_a_3125_);
return v___x_3475_;
}
case 1:
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_nCtx_3122_);
v_a_3476_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3478_ = v_a_3124_;
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v_a_3124_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3480_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__10));
v___x_3481_ = l_Lean_mkMVar(v_a_3476_);
v___x_3482_ = lean_expr_dbg_to_string(v___x_3481_);
lean_dec_ref(v___x_3481_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 3);
lean_ctor_set(v___x_3478_, 0, v___x_3482_);
v___x_3484_ = v___x_3478_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3480_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v_a_3125_);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
case 2:
{
lean_object* v_a_3490_; lean_object* v_a_3491_; 
v_a_3490_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3490_);
v_a_3491_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3491_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3354_ = v_a_3123_;
v_wi_3355_ = v_a_3490_;
v_d_3356_ = v_a_3491_;
v___y_3357_ = v_a_3125_;
goto v___jp_3353_;
}
case 3:
{
lean_object* v_a_3492_; lean_object* v_a_3493_; 
v_a_3492_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3492_);
v_a_3493_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3493_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3398_ = v_a_3492_;
v_d_3399_ = v_a_3493_;
v___y_3400_ = v_a_3125_;
goto v___jp_3397_;
}
case 4:
{
lean_object* v_a_3494_; lean_object* v_a_3495_; 
lean_dec_ref(v_nCtx_3122_);
v_a_3494_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3494_);
v_a_3495_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3495_);
lean_dec_ref_known(v_a_3124_, 2);
v_nCtx_3122_ = v_a_3494_;
v_a_3124_ = v_a_3495_;
goto _start;
}
case 5:
{
lean_object* v_a_3497_; lean_object* v_a_3498_; 
v_a_3497_ = lean_ctor_get(v_a_3124_, 0);
lean_inc(v_a_3497_);
v_a_3498_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3498_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3329_ = v_a_3123_;
v_n_3330_ = v_a_3497_;
v_d_3331_ = v_a_3498_;
v___y_3332_ = v_a_3125_;
goto v___jp_3328_;
}
case 6:
{
lean_object* v_a_3499_; 
v_a_3499_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3499_);
lean_dec_ref_known(v_a_3124_, 1);
v_ctx_3438_ = v_a_3123_;
v_d_3439_ = v_a_3499_;
v___y_3440_ = v_a_3125_;
goto v___jp_3437_;
}
case 7:
{
lean_object* v_a_3500_; lean_object* v_a_3501_; 
v_a_3500_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3500_);
v_a_3501_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3501_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3404_ = v_a_3123_;
v_d_u2081_3405_ = v_a_3500_;
v_d_u2082_3406_ = v_a_3501_;
v___y_3407_ = v_a_3125_;
goto v___jp_3403_;
}
case 9:
{
lean_object* v_data_3502_; lean_object* v_msg_3503_; lean_object* v_children_3504_; 
v_data_3502_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_data_3502_);
v_msg_3503_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_msg_3503_);
v_children_3504_ = lean_ctor_get(v_a_3124_, 2);
lean_inc_ref(v_children_3504_);
lean_dec_ref_known(v_a_3124_, 3);
v_ctx_3262_ = v_a_3123_;
v_data_3263_ = v_data_3502_;
v_header_3264_ = v_msg_3503_;
v_children_3265_ = v_children_3504_;
v___y_3266_ = v_a_3125_;
goto v___jp_3261_;
}
case 10:
{
lean_object* v_f_3505_; lean_object* v___x_3506_; 
v_f_3505_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_f_3505_);
lean_dec_ref_known(v_a_3124_, 2);
v___x_3506_ = lean_box(0);
v___y_3463_ = v_a_3125_;
v___y_3464_ = v_a_3123_;
v___y_3465_ = v_f_3505_;
v___y_3466_ = v___x_3506_;
goto v___jp_3462_;
}
default: 
{
lean_object* v_a_3507_; 
v_a_3507_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3507_);
lean_dec_ref(v_a_3124_);
v_a_3124_ = v_a_3507_;
goto _start;
}
}
}
else
{
switch(lean_obj_tag(v_a_3124_))
{
case 0:
{
lean_object* v_a_3509_; lean_object* v_val_3510_; lean_object* v_fmt_3511_; lean_object* v_infos_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3547_; 
v_a_3509_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3509_);
lean_dec_ref_known(v_a_3124_, 1);
v_val_3510_ = lean_ctor_get(v_a_3123_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_a_3123_, 1);
v_fmt_3511_ = lean_ctor_get(v_a_3509_, 0);
v_infos_3512_ = lean_ctor_get(v_a_3509_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3514_ = v_a_3509_;
v_isShared_3515_ = v_isSharedCheck_3547_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_infos_3512_);
lean_inc(v_fmt_3511_);
lean_dec(v_a_3509_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3547_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3122_, v_val_3510_);
lean_dec(v_val_3510_);
lean_dec_ref(v_nCtx_3122_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3516_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_infos_3512_);
v___x_3518_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3518_, v_a_3125_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3537_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3537_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3537_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v_fst_3524_; lean_object* v_snd_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3536_; 
v_fst_3524_ = lean_ctor_get(v_a_3520_, 0);
v_snd_3525_ = lean_ctor_get(v_a_3520_, 1);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3527_ = v_a_3520_;
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_snd_3525_);
lean_inc(v_fst_3524_);
lean_dec(v_a_3520_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3536_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_fst_3524_);
lean_ctor_set(v___x_3529_, 1, v_fmt_3511_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_snd_3525_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3531_);
v___x_3533_ = v___x_3522_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_fmt_3511_);
v_a_3538_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3519_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3519_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
case 1:
{
lean_object* v_val_3548_; lean_object* v_a_3549_; lean_object* v_lctx_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v_val_3548_ = lean_ctor_get(v_a_3123_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_a_3123_, 1);
v_a_3549_ = lean_ctor_get(v_a_3124_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v_a_3124_, 1);
v_lctx_3550_ = lean_ctor_get(v_val_3548_, 2);
lean_inc_ref(v_lctx_3550_);
v___x_3551_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3122_, v_val_3548_);
lean_dec(v_val_3548_);
lean_dec_ref(v_nCtx_3122_);
v___x_3552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v_lctx_3550_);
lean_ctor_set(v___x_3552_, 2, v_a_3549_);
v___x_3553_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3552_, v_a_3125_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3572_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3572_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3572_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v_fst_3558_; lean_object* v_snd_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3571_; 
v_fst_3558_ = lean_ctor_get(v_a_3554_, 0);
v_snd_3559_ = lean_ctor_get(v_a_3554_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_a_3554_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3561_ = v_a_3554_;
v_isShared_3562_ = v_isSharedCheck_3571_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_snd_3559_);
lean_inc(v_fst_3558_);
lean_dec(v_a_3554_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3571_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_fst_3558_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_snd_3559_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3566_);
v___x_3568_ = v___x_3556_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3553_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3553_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
case 2:
{
lean_object* v_a_3581_; lean_object* v_a_3582_; 
v_a_3581_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3581_);
v_a_3582_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3582_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3354_ = v_a_3123_;
v_wi_3355_ = v_a_3581_;
v_d_3356_ = v_a_3582_;
v___y_3357_ = v_a_3125_;
goto v___jp_3353_;
}
case 3:
{
lean_object* v_a_3583_; lean_object* v_a_3584_; 
lean_dec_ref_known(v_a_3123_, 1);
v_a_3583_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3583_);
v_a_3584_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3584_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3398_ = v_a_3583_;
v_d_3399_ = v_a_3584_;
v___y_3400_ = v_a_3125_;
goto v___jp_3397_;
}
case 4:
{
lean_object* v_a_3585_; lean_object* v_a_3586_; 
lean_dec_ref(v_nCtx_3122_);
v_a_3585_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3585_);
v_a_3586_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3586_);
lean_dec_ref_known(v_a_3124_, 2);
v_nCtx_3122_ = v_a_3585_;
v_a_3124_ = v_a_3586_;
goto _start;
}
case 5:
{
lean_object* v_a_3588_; lean_object* v_a_3589_; 
v_a_3588_ = lean_ctor_get(v_a_3124_, 0);
lean_inc(v_a_3588_);
v_a_3589_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3589_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3329_ = v_a_3123_;
v_n_3330_ = v_a_3588_;
v_d_3331_ = v_a_3589_;
v___y_3332_ = v_a_3125_;
goto v___jp_3328_;
}
case 6:
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3590_);
lean_dec_ref_known(v_a_3124_, 1);
v_ctx_3438_ = v_a_3123_;
v_d_3439_ = v_a_3590_;
v___y_3440_ = v_a_3125_;
goto v___jp_3437_;
}
case 7:
{
lean_object* v_a_3591_; lean_object* v_a_3592_; 
v_a_3591_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_a_3591_);
v_a_3592_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3592_);
lean_dec_ref_known(v_a_3124_, 2);
v_ctx_3404_ = v_a_3123_;
v_d_u2081_3405_ = v_a_3591_;
v_d_u2082_3406_ = v_a_3592_;
v___y_3407_ = v_a_3125_;
goto v___jp_3403_;
}
case 9:
{
lean_object* v_data_3593_; lean_object* v_msg_3594_; lean_object* v_children_3595_; 
v_data_3593_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_data_3593_);
v_msg_3594_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_msg_3594_);
v_children_3595_ = lean_ctor_get(v_a_3124_, 2);
lean_inc_ref(v_children_3595_);
lean_dec_ref_known(v_a_3124_, 3);
v_ctx_3262_ = v_a_3123_;
v_data_3263_ = v_data_3593_;
v_header_3264_ = v_msg_3594_;
v_children_3265_ = v_children_3595_;
v___y_3266_ = v_a_3125_;
goto v___jp_3261_;
}
case 10:
{
lean_object* v_val_3596_; lean_object* v_f_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_val_3596_ = lean_ctor_get(v_a_3123_, 0);
v_f_3597_ = lean_ctor_get(v_a_3124_, 0);
lean_inc_ref(v_f_3597_);
lean_dec_ref_known(v_a_3124_, 2);
v___x_3598_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_3122_, v_val_3596_);
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
v___y_3463_ = v_a_3125_;
v___y_3464_ = v_a_3123_;
v___y_3465_ = v_f_3597_;
v___y_3466_ = v___x_3599_;
goto v___jp_3462_;
}
default: 
{
lean_object* v_a_3600_; 
v_a_3600_ = lean_ctor_get(v_a_3124_, 1);
lean_inc_ref(v_a_3600_);
lean_dec_ref(v_a_3124_);
v_a_3124_ = v_a_3600_;
goto _start;
}
}
}
v___jp_3127_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3133_, 0, v___y_3129_);
lean_ctor_set(v___x_3133_, 1, v___y_3130_);
lean_ctor_set(v___x_3133_, 2, v_nodes_3131_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*3, v___y_3128_);
v___x_3134_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3133_, v___y_3132_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3153_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3153_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3153_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v_fst_3139_; lean_object* v_snd_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3152_; 
v_fst_3139_ = lean_ctor_get(v_a_3135_, 0);
v_snd_3140_ = lean_ctor_get(v_a_3135_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_3135_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3142_ = v_a_3135_;
v_isShared_3143_ = v_isSharedCheck_3152_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_snd_3140_);
lean_inc(v_fst_3139_);
lean_dec(v_a_3135_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3152_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_fst_3139_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3145_);
v___x_3147_ = v___x_3142_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_snd_3140_);
v___x_3147_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3149_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3147_);
v___x_3149_ = v___x_3137_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3134_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3134_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
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
v___jp_3162_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_array_get_size(v___y_3166_);
v___x_3171_ = l_Array_toSubarray___redArg(v___y_3166_, v___x_3169_, v___x_3170_);
lean_inc(v___y_3165_);
v___x_3172_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v___y_3165_, v___y_3168_, v___x_3171_);
lean_dec(v___y_3168_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
v___y_3128_ = v___y_3163_;
v___y_3129_ = v___y_3165_;
v___y_3130_ = v___y_3167_;
v_nodes_3131_ = v___x_3173_;
v___y_3132_ = v___y_3164_;
goto v___jp_3127_;
}
v___jp_3174_:
{
lean_object* v___x_3180_; lean_object* v_defValue_3181_; 
v___x_3180_ = l_Lean_MessageData_maxTraceChildren;
v_defValue_3181_ = lean_ctor_get(v___x_3180_, 1);
lean_inc(v_defValue_3181_);
v___y_3163_ = v___y_3175_;
v___y_3164_ = v___y_3177_;
v___y_3165_ = v___y_3176_;
v___y_3166_ = v___y_3178_;
v___y_3167_ = v___y_3179_;
v___y_3168_ = v_defValue_3181_;
goto v___jp_3162_;
}
v___jp_3182_:
{
size_t v_sz_3189_; size_t v___x_3190_; lean_object* v___x_3191_; 
v_sz_3189_ = lean_array_size(v___y_3187_);
v___x_3190_ = ((size_t)0ULL);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v___y_3188_, v_nCtx_3122_, v_sz_3189_, v___x_3190_, v___y_3187_);
if (lean_obj_tag(v___y_3188_) == 0)
{
v___y_3175_ = v___y_3183_;
v___y_3176_ = v___y_3184_;
v___y_3177_ = v___y_3185_;
v___y_3178_ = v___x_3191_;
v___y_3179_ = v___y_3186_;
goto v___jp_3174_;
}
else
{
lean_object* v_val_3192_; lean_object* v_opts_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_val_3192_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v___y_3188_, 1);
v_opts_3193_ = lean_ctor_get(v_val_3192_, 3);
lean_inc_ref(v_opts_3193_);
lean_dec(v_val_3192_);
v___x_3194_ = l_Lean_MessageData_maxTraceChildren;
v___x_3195_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3193_, v___x_3194_);
lean_dec_ref(v_opts_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
v___y_3175_ = v___y_3183_;
v___y_3176_ = v___y_3184_;
v___y_3177_ = v___y_3185_;
v___y_3178_ = v___x_3191_;
v___y_3179_ = v___y_3186_;
goto v___jp_3174_;
}
else
{
lean_object* v_val_3196_; 
v_val_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_val_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___y_3163_ = v___y_3183_;
v___y_3164_ = v___y_3185_;
v___y_3165_ = v___y_3184_;
v___y_3166_ = v___x_3191_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v_val_3196_;
goto v___jp_3162_;
}
}
}
v___jp_3197_:
{
if (v___y_3204_ == 0)
{
size_t v_sz_3205_; size_t v___x_3206_; lean_object* v___x_3207_; 
v_sz_3205_ = lean_array_size(v___y_3202_);
v___x_3206_ = ((size_t)0ULL);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3122_, v___y_3203_, v_sz_3205_, v___x_3206_, v___y_3202_, v___y_3200_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_fst_3209_; lean_object* v_snd_3210_; lean_object* v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v_fst_3209_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_fst_3209_);
v_snd_3210_ = lean_ctor_get(v_a_3208_, 1);
lean_inc(v_snd_3210_);
lean_dec(v_a_3208_);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v_fst_3209_);
v___y_3128_ = v___y_3198_;
v___y_3129_ = v___y_3199_;
v___y_3130_ = v___y_3201_;
v_nodes_3131_ = v___x_3211_;
v___y_3132_ = v_snd_3210_;
goto v___jp_3127_;
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___y_3201_);
lean_dec(v___y_3199_);
v_a_3212_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3207_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3207_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
v___y_3183_ = v___y_3198_;
v___y_3184_ = v___y_3199_;
v___y_3185_ = v___y_3200_;
v___y_3186_ = v___y_3201_;
v___y_3187_ = v___y_3202_;
v___y_3188_ = v___y_3203_;
goto v___jp_3182_;
}
}
v___jp_3220_:
{
if (v___y_3222_ == 0)
{
v___y_3198_ = v___y_3222_;
v___y_3199_ = v___y_3223_;
v___y_3200_ = v___y_3227_;
v___y_3201_ = v_header_3226_;
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3221_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3228_ = lean_array_get_size(v___y_3224_);
v___x_3229_ = lean_unsigned_to_nat(0u);
v___x_3230_ = lean_nat_dec_eq(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
v___y_3183_ = v___y_3222_;
v___y_3184_ = v___y_3223_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v_header_3226_;
v___y_3187_ = v___y_3224_;
v___y_3188_ = v___y_3225_;
goto v___jp_3182_;
}
else
{
v___y_3198_ = v___y_3222_;
v___y_3199_ = v___y_3223_;
v___y_3200_ = v___y_3227_;
v___y_3201_ = v_header_3226_;
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3221_;
goto v___jp_3197_;
}
}
}
v___jp_3231_:
{
lean_object* v___x_3241_; double v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3241_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1));
v___x_3242_ = lean_float_sub(v___y_3238_, v___y_3233_);
v___x_3243_ = lean_float_to_string(v___x_3242_);
v___x_3244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3241_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3));
v___x_3247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
lean_ctor_set(v___x_3248_, 1, v___y_3236_);
v___y_3221_ = v___y_3235_;
v___y_3222_ = v___y_3234_;
v___y_3223_ = v___y_3237_;
v___y_3224_ = v___y_3239_;
v___y_3225_ = v___y_3240_;
v_header_3226_ = v___x_3248_;
v___y_3227_ = v___y_3232_;
goto v___jp_3220_;
}
v___jp_3249_:
{
double v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3260_ = lean_float_beq(v___y_3251_, v___x_3259_);
if (v___x_3260_ == 0)
{
v___y_3232_ = v___y_3250_;
v___y_3233_ = v___y_3251_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3252_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3254_;
v___y_3238_ = v___y_3255_;
v___y_3239_ = v___y_3256_;
v___y_3240_ = v___y_3257_;
goto v___jp_3231_;
}
else
{
if (v___y_3252_ == 0)
{
v___y_3221_ = v___y_3252_;
v___y_3222_ = v___y_3253_;
v___y_3223_ = v___y_3254_;
v___y_3224_ = v___y_3256_;
v___y_3225_ = v___y_3257_;
v_header_3226_ = v___y_3258_;
v___y_3227_ = v___y_3250_;
goto v___jp_3220_;
}
else
{
v___y_3232_ = v___y_3250_;
v___y_3233_ = v___y_3251_;
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3252_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3254_;
v___y_3238_ = v___y_3255_;
v___y_3239_ = v___y_3256_;
v___y_3240_ = v___y_3257_;
goto v___jp_3231_;
}
}
}
v___jp_3261_:
{
lean_object* v_cls_3267_; lean_object* v_result_x3f_3268_; double v_startTime_3269_; double v_stopTime_3270_; uint8_t v_collapsed_3271_; uint8_t v___x_3272_; 
v_cls_3267_ = lean_ctor_get(v_data_3263_, 0);
lean_inc(v_cls_3267_);
v_result_x3f_3268_ = lean_ctor_get(v_data_3263_, 1);
lean_inc(v_result_x3f_3268_);
v_startTime_3269_ = lean_ctor_get_float(v_data_3263_, sizeof(void*)*3);
v_stopTime_3270_ = lean_ctor_get_float(v_data_3263_, sizeof(void*)*3 + 8);
v_collapsed_3271_ = lean_ctor_get_uint8(v_data_3263_, sizeof(void*)*3 + 16);
lean_dec_ref(v_data_3263_);
v___x_3272_ = l_Lean_Name_isAnonymous(v_cls_3267_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_inc(v_ctx_3262_);
lean_inc_ref(v_nCtx_3122_);
v___x_3273_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3262_, v_header_3264_, v___y_3266_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3297_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_fst_3275_ = lean_ctor_get(v_a_3274_, 0);
v_snd_3276_ = lean_ctor_get(v_a_3274_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_a_3274_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3278_ = v_a_3274_;
v_isShared_3279_ = v_isSharedCheck_3297_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snd_3276_);
lean_inc(v_fst_3275_);
lean_dec(v_a_3274_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3297_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4);
if (v_isShared_3279_ == 0)
{
lean_ctor_set_tag(v___x_3278_, 4);
lean_ctor_set(v___x_3278_, 1, v_fst_3275_);
lean_ctor_set(v___x_3278_, 0, v___x_3280_);
v___x_3282_ = v___x_3278_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_fst_3275_);
v___x_3282_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
if (lean_obj_tag(v_result_x3f_3268_) == 0)
{
v___y_3250_ = v_snd_3276_;
v___y_3251_ = v_startTime_3269_;
v___y_3252_ = v___x_3272_;
v___y_3253_ = v_collapsed_3271_;
v___y_3254_ = v_cls_3267_;
v___y_3255_ = v_stopTime_3270_;
v___y_3256_ = v_children_3265_;
v___y_3257_ = v_ctx_3262_;
v___y_3258_ = v___x_3282_;
goto v___jp_3249_;
}
else
{
lean_object* v_val_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3295_; 
v_val_3283_ = lean_ctor_get(v_result_x3f_3268_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_result_x3f_3268_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3285_ = v_result_x3f_3268_;
v_isShared_3286_ = v_isSharedCheck_3295_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_val_3283_);
lean_dec(v_result_x3f_3268_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3295_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = lean_unbox(v_val_3283_);
lean_dec(v_val_3283_);
v___x_3288_ = l_Lean_TraceResult_toEmoji(v___x_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 3);
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6));
v___x_3292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v___x_3282_);
v___y_3250_ = v_snd_3276_;
v___y_3251_ = v_startTime_3269_;
v___y_3252_ = v___x_3272_;
v___y_3253_ = v_collapsed_3271_;
v___y_3254_ = v_cls_3267_;
v___y_3255_ = v_stopTime_3270_;
v___y_3256_ = v_children_3265_;
v___y_3257_ = v_ctx_3262_;
v___y_3258_ = v___x_3293_;
goto v___jp_3249_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_3268_);
lean_dec(v_cls_3267_);
lean_dec_ref(v_children_3265_);
lean_dec(v_ctx_3262_);
lean_dec_ref(v_nCtx_3122_);
return v___x_3273_;
}
}
else
{
size_t v_sz_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_result_x3f_3268_);
lean_dec(v_cls_3267_);
lean_dec_ref(v_header_3264_);
v_sz_3298_ = lean_array_size(v_children_3265_);
v___x_3299_ = ((size_t)0ULL);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3122_, v_ctx_3262_, v_sz_3298_, v___x_3299_, v_children_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3319_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3319_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3319_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3318_; 
v_fst_3305_ = lean_ctor_get(v_a_3301_, 0);
v_snd_3306_ = lean_ctor_get(v_a_3301_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3308_ = v_a_3301_;
v_isShared_3309_ = v_isSharedCheck_3318_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_snd_3306_);
lean_inc(v_fst_3305_);
lean_dec(v_a_3301_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3318_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3310_ = lean_array_to_list(v_fst_3305_);
v___x_3311_ = l_Std_Format_join(v___x_3310_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3311_);
v___x_3313_ = v___x_3308_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_snd_3306_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3313_);
v___x_3315_ = v___x_3303_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
v_a_3320_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3300_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3300_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
v___jp_3328_:
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3329_, v_d_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3352_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3352_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3352_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_fst_3338_; lean_object* v_snd_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3351_; 
v_fst_3338_ = lean_ctor_get(v_a_3334_, 0);
v_snd_3339_ = lean_ctor_get(v_a_3334_, 1);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3341_ = v_a_3334_;
v_isShared_3342_ = v_isSharedCheck_3351_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_snd_3339_);
lean_inc(v_fst_3338_);
lean_dec(v_a_3334_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3351_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3343_ = lean_nat_to_int(v_n_3330_);
v___x_3344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v_fst_3338_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3344_);
v___x_3346_ = v___x_3341_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_snd_3339_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3346_);
v___x_3348_ = v___x_3336_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
else
{
lean_dec(v_n_3330_);
return v___x_3333_;
}
}
v___jp_3353_:
{
lean_object* v___x_3358_; 
v___x_3358_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3354_, v_d_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3396_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_fst_3360_ = lean_ctor_get(v_a_3359_, 0);
v_snd_3361_ = lean_ctor_get(v_a_3359_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3359_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3363_ = v_a_3359_;
v_isShared_3364_ = v_isSharedCheck_3396_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_snd_3361_);
lean_inc(v_fst_3360_);
lean_dec(v_a_3359_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3396_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 2);
lean_ctor_set(v___x_3363_, 1, v_fst_3360_);
lean_ctor_set(v___x_3363_, 0, v_wi_3355_);
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_wi_3355_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_fst_3360_);
v___x_3366_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3366_, v_snd_3361_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3386_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3386_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3386_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3385_; 
v_fst_3372_ = lean_ctor_get(v_a_3368_, 0);
v_snd_3373_ = lean_ctor_get(v_a_3368_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3375_ = v_a_3368_;
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v_a_3368_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3385_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_fst_3372_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_snd_3373_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3382_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3380_);
v___x_3382_ = v___x_3370_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_a_3387_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3367_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3367_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_wi_3355_);
return v___x_3358_;
}
}
v___jp_3397_:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_ctx_3398_);
v_a_3123_ = v___x_3401_;
v_a_3124_ = v_d_3399_;
v_a_3125_ = v___y_3400_;
goto _start;
}
v___jp_3403_:
{
lean_object* v___x_3408_; 
lean_inc(v_ctx_3404_);
lean_inc_ref(v_nCtx_3122_);
v___x_3408_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3404_, v_d_u2081_3405_, v___y_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3436_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v_fst_3410_ = lean_ctor_get(v_a_3409_, 0);
v_snd_3411_ = lean_ctor_get(v_a_3409_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_a_3409_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3413_ = v_a_3409_;
v_isShared_3414_ = v_isSharedCheck_3436_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_inc(v_fst_3410_);
lean_dec(v_a_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3436_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3404_, v_d_u2082_3406_, v_snd_3411_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3435_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3435_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3435_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3434_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
v_snd_3421_ = lean_ctor_get(v_a_3416_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3423_ = v_a_3416_;
v_isShared_3424_ = v_isSharedCheck_3434_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3434_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 5);
lean_ctor_set(v___x_3413_, 1, v_fst_3420_);
v___x_3426_ = v___x_3413_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_fst_3410_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_fst_3420_);
v___x_3426_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3426_);
v___x_3428_ = v___x_3423_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_snd_3421_);
v___x_3428_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3428_);
v___x_3430_ = v___x_3418_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3413_);
lean_dec(v_fst_3410_);
return v___x_3415_;
}
}
}
else
{
lean_dec_ref(v_d_u2082_3406_);
lean_dec(v_ctx_3404_);
lean_dec_ref(v_nCtx_3122_);
return v___x_3408_;
}
}
v___jp_3437_:
{
lean_object* v___x_3441_; 
v___x_3441_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_ctx_3438_, v_d_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3460_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3460_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3460_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v_fst_3446_; lean_object* v_snd_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3459_; 
v_fst_3446_ = lean_ctor_get(v_a_3442_, 0);
v_snd_3447_ = lean_ctor_get(v_a_3442_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_a_3442_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3449_ = v_a_3442_;
v_isShared_3450_ = v_isSharedCheck_3459_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_snd_3447_);
lean_inc(v_fst_3446_);
lean_dec(v_a_3442_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3459_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3451_ = 0;
v___x_3452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3452_, 0, v_fst_3446_);
lean_ctor_set_uint8(v___x_3452_, sizeof(void*)*1, v___x_3451_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3452_);
v___x_3454_ = v___x_3449_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3447_);
v___x_3454_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3454_);
v___x_3456_ = v___x_3444_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
else
{
return v___x_3441_;
}
}
v___jp_3462_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_apply_2(v___y_3465_, v___y_3466_, lean_box(0));
v___x_3468_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_3467_, v___x_3461_);
lean_dec(v___x_3467_);
if (lean_obj_tag(v___x_3468_) == 1)
{
lean_object* v_val_3469_; 
v_val_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_val_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v_a_3123_ = v___y_3464_;
v_a_3124_ = v_val_3469_;
v_a_3125_ = v___y_3463_;
goto _start;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_dec(v___x_3468_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v_nCtx_3122_);
v___x_3471_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
return v___x_3472_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_nCtx_3122_ = stack[0].m_obj;
lean_object* v_a_3123_ = stack[1].m_obj;
lean_object* v_a_3124_ = stack[2].m_obj;
lean_object* v_a_3125_ = stack[3].m_obj;
lean_object* v_res_3602_;
v_res_3602_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
stack->m_obj
 = v_res_3602_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object* v_nCtx_3603_, lean_object* v_ctx_3604_, size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_bs_3607_, lean_object* v___y_3608_){
_start:
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_usize_dec_lt(v_i_3606_, v_sz_3605_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_dec(v_ctx_3604_);
lean_dec_ref(v_nCtx_3603_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_bs_3607_);
lean_ctor_set(v___x_3611_, 1, v___y_3608_);
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
return v___x_3612_;
}
else
{
lean_object* v_v_3613_; lean_object* v___x_3614_; lean_object* v_bs_x27_3615_; lean_object* v___x_3616_; 
v_v_3613_ = lean_array_uget(v_bs_3607_, v_i_3606_);
v___x_3614_ = lean_unsigned_to_nat(0u);
v_bs_x27_3615_ = lean_array_uset(v_bs_3607_, v_i_3606_, v___x_3614_);
lean_inc(v_ctx_3604_);
lean_inc_ref(v_nCtx_3603_);
v___x_3616_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3603_, v_ctx_3604_, v_v_3613_, v___y_3608_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v_fst_3618_; lean_object* v_snd_3619_; size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v_fst_3618_ = lean_ctor_get(v_a_3617_, 0);
lean_inc(v_fst_3618_);
v_snd_3619_ = lean_ctor_get(v_a_3617_, 1);
lean_inc(v_snd_3619_);
lean_dec(v_a_3617_);
v___x_3620_ = ((size_t)1ULL);
v___x_3621_ = lean_usize_add(v_i_3606_, v___x_3620_);
v___x_3622_ = lean_array_uset(v_bs_x27_3615_, v_i_3606_, v_fst_3618_);
v_i_3606_ = v___x_3621_;
v_bs_3607_ = v___x_3622_;
v___y_3608_ = v_snd_3619_;
goto _start;
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_bs_x27_3615_);
lean_dec(v_ctx_3604_);
lean_dec_ref(v_nCtx_3603_);
v_a_3624_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3616_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3616_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_nCtx_3603_ = stack[0].m_obj;
lean_object* v_ctx_3604_ = stack[1].m_obj;
size_t v_sz_3605_ = stack[2].m_num;
size_t v_i_3606_ = stack[3].m_num;
lean_object* v_bs_3607_ = stack[4].m_obj;
lean_object* v___y_3608_ = stack[5].m_obj;
lean_object* v_res_3632_;
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3603_, v_ctx_3604_, v_sz_3605_, v_i_3606_, v_bs_3607_, v___y_3608_);
stack->m_obj
 = v_res_3632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3___boxed(lean_object* v_nCtx_3633_, lean_object* v_ctx_3634_, lean_object* v_sz_3635_, lean_object* v_i_3636_, lean_object* v_bs_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
size_t v_sz_boxed_3640_; size_t v_i_boxed_3641_; lean_object* v_res_3642_; 
v_sz_boxed_3640_ = lean_unbox_usize(v_sz_3635_);
lean_dec(v_sz_3635_);
v_i_boxed_3641_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_res_3642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3633_, v_ctx_3634_, v_sz_boxed_3640_, v_i_boxed_3641_, v_bs_3637_, v___y_3638_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object* v_nCtx_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
return v_res_3648_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object* v_msgData_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3656_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0));
v___x_3657_ = lean_box(0);
v___x_3658_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1));
v___x_3659_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v___x_3656_, v___x_3657_, v_msgData_3654_, v___x_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3654_ = stack[0].m_obj;
lean_object* v_res_3660_;
v_res_3660_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3654_);
stack->m_obj
 = v_res_3660_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object* v_msgData_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3661_);
return v_res_3663_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object* v_g_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Widget_goalToInteractive(v_g_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3681_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3675_, 0, v_a_3671_);
v___x_3676_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
v___x_3677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3677_);
v___x_3679_ = v___x_3673_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3682_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3670_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3670_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_3664_ = stack[0].m_obj;
lean_object* v___y_3665_ = stack[1].m_obj;
lean_object* v___y_3666_ = stack[2].m_obj;
lean_object* v___y_3667_ = stack[3].m_obj;
lean_object* v___y_3668_ = stack[4].m_obj;
lean_object* v_res_3690_;
v_res_3690_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(v_g_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
stack->m_obj
 = v_res_3690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object* v_g_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(v_g_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object* v_f_3698_, size_t v_sz_3699_, size_t v_i_3700_, lean_object* v_bs_3701_){
_start:
{
uint8_t v___x_3703_; 
v___x_3703_ = lean_usize_dec_lt(v_i_3700_, v_sz_3699_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec_ref(v_f_3698_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v_bs_3701_);
return v___x_3704_;
}
else
{
lean_object* v_v_3705_; lean_object* v___x_3706_; lean_object* v_bs_x27_3707_; lean_object* v___x_3708_; 
v_v_3705_ = lean_array_uget(v_bs_3701_, v_i_3700_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v_bs_x27_3707_ = lean_array_uset(v_bs_3701_, v_i_3700_, v___x_3706_);
lean_inc_ref(v_f_3698_);
v___x_3708_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3698_, v_v_3705_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; size_t v___x_3710_; size_t v___x_3711_; lean_object* v___x_3712_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = ((size_t)1ULL);
v___x_3711_ = lean_usize_add(v_i_3700_, v___x_3710_);
v___x_3712_ = lean_array_uset(v_bs_x27_3707_, v_i_3700_, v_a_3709_);
v_i_3700_ = v___x_3711_;
v_bs_3701_ = v___x_3712_;
goto _start;
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v_bs_x27_3707_);
lean_dec_ref(v_f_3698_);
v_a_3714_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3708_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3708_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3698_ = stack[0].m_obj;
size_t v_sz_3699_ = stack[1].m_num;
size_t v_i_3700_ = stack[2].m_num;
lean_object* v_bs_3701_ = stack[3].m_obj;
lean_object* v_res_3722_;
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3698_, v_sz_3699_, v_i_3700_, v_bs_3701_);
stack->m_obj
 = v_res_3722_;
}
lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object* v_f_3723_, lean_object* v_x_3724_){
_start:
{
switch(lean_obj_tag(v_x_3724_))
{
case 0:
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v_f_3723_);
v_a_3726_ = lean_ctor_get(v_x_3724_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_x_3724_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3728_ = v_x_3724_;
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v_x_3724_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
}
case 1:
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3761_; 
v_a_3735_ = lean_ctor_get(v_x_3724_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_x_3724_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3737_ = v_x_3724_;
v_isShared_3738_ = v_isSharedCheck_3761_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v_x_3724_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3761_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
size_t v_sz_3739_; size_t v___x_3740_; lean_object* v___x_3741_; 
v_sz_3739_ = lean_array_size(v_a_3735_);
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3723_, v_sz_3739_, v___x_3740_, v_a_3735_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3752_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3752_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_a_3742_);
v___x_3747_ = v___x_3737_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3747_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3737_);
v_a_3753_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3741_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3741_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
default: 
{
lean_object* v_a_3762_; lean_object* v_a_3763_; lean_object* v___x_3764_; 
v_a_3762_ = lean_ctor_get(v_x_3724_, 0);
lean_inc(v_a_3762_);
v_a_3763_ = lean_ctor_get(v_x_3724_, 1);
lean_inc_ref(v_a_3763_);
lean_dec_ref_known(v_x_3724_, 2);
v___x_3764_ = lean_apply_3(v_f_3723_, v_a_3762_, v_a_3763_, lean_box(0));
return v___x_3764_;
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3723_ = stack[0].m_obj;
lean_object* v_x_3724_ = stack[1].m_obj;
lean_object* v_res_3765_;
v_res_3765_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3723_, v_x_3724_);
stack->m_obj
 = v_res_3765_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg___boxed(lean_object* v_f_3766_, lean_object* v_x_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3766_, v_x_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object* v_f_3770_, lean_object* v_sz_3771_, lean_object* v_i_3772_, lean_object* v_bs_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3771_);
lean_dec(v_sz_3771_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3772_);
lean_dec(v_i_3772_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3770_, v_sz_boxed_3775_, v_i_boxed_3776_, v_bs_3773_);
return v_res_3777_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_bs_3780_){
_start:
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_usize_dec_lt(v_i_3779_, v_sz_3778_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_bs_3780_);
return v___x_3783_;
}
else
{
lean_object* v_v_3784_; lean_object* v___x_3785_; lean_object* v_bs_x27_3786_; lean_object* v___x_3787_; size_t v___x_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v_v_3784_ = lean_array_uget(v_bs_3780_, v_i_3779_);
v___x_3785_ = lean_unsigned_to_nat(0u);
v_bs_x27_3786_ = lean_array_uset(v_bs_3780_, v_i_3779_, v___x_3785_);
v___x_3787_ = l_Lean_Server_WithRpcRef_mk___redArg(v_v_3784_);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3779_, v___x_3788_);
v___x_3790_ = lean_array_uset(v_bs_x27_3786_, v_i_3779_, v___x_3787_);
v_i_3779_ = v___x_3789_;
v_bs_3780_ = v___x_3790_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3778_ = stack[0].m_num;
size_t v_i_3779_ = stack[1].m_num;
lean_object* v_bs_3780_ = stack[2].m_obj;
lean_object* v_res_3792_;
v_res_3792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_3778_, v_i_3779_, v_bs_3780_);
stack->m_obj
 = v_res_3792_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object* v_sz_3793_, lean_object* v_i_3794_, lean_object* v_bs_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3793_);
lean_dec(v_sz_3793_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3794_);
lean_dec(v_i_3794_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_boxed_3797_, v_i_boxed_3798_, v_bs_3795_);
return v_res_3799_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object* v_col_3800_, lean_object* v_embeds_3801_, size_t v_sz_3802_, size_t v_i_3803_, lean_object* v_bs_3804_){
_start:
{
uint8_t v___x_3806_; 
v___x_3806_ = lean_usize_dec_lt(v_i_3803_, v_sz_3802_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; 
lean_dec_ref(v_embeds_3801_);
v___x_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3807_, 0, v_bs_3804_);
return v___x_3807_;
}
else
{
lean_object* v_v_3808_; lean_object* v___x_3809_; lean_object* v_bs_x27_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_v_3808_ = lean_array_uget(v_bs_3804_, v_i_3803_);
v___x_3809_ = lean_unsigned_to_nat(0u);
v_bs_x27_3810_ = lean_array_uset(v_bs_3804_, v_i_3803_, v___x_3809_);
v___x_3811_ = lean_unsigned_to_nat(2u);
v___x_3812_ = lean_nat_add(v_col_3800_, v___x_3811_);
lean_inc_ref(v_embeds_3801_);
v___x_3813_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3801_, v_v_3808_, v___x_3812_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___x_3815_ = ((size_t)1ULL);
v___x_3816_ = lean_usize_add(v_i_3803_, v___x_3815_);
v___x_3817_ = lean_array_uset(v_bs_x27_3810_, v_i_3803_, v_a_3814_);
v_i_3803_ = v___x_3816_;
v_bs_3804_ = v___x_3817_;
goto _start;
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_bs_x27_3810_);
lean_dec_ref(v_embeds_3801_);
v_a_3819_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3813_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3813_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_col_3800_ = stack[0].m_obj;
lean_object* v_embeds_3801_ = stack[1].m_obj;
size_t v_sz_3802_ = stack[2].m_num;
size_t v_i_3803_ = stack[3].m_num;
lean_object* v_bs_3804_ = stack[4].m_obj;
lean_object* v_res_3827_;
v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3800_, v_embeds_3801_, v_sz_3802_, v_i_3803_, v_bs_3804_);
stack->m_obj
 = v_res_3827_;
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object* v___x_3828_, lean_object* v_embeds_3829_, lean_object* v_indent_3830_, lean_object* v_x_3831_, lean_object* v_tt_3832_){
_start:
{
lean_object* v_fst_3834_; lean_object* v_snd_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3948_; 
v_fst_3834_ = lean_ctor_get(v_x_3831_, 0);
v_snd_3835_ = lean_ctor_get(v_x_3831_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_x_3831_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3837_ = v_x_3831_;
v_isShared_3838_ = v_isSharedCheck_3948_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_snd_3835_);
lean_inc(v_fst_3834_);
lean_dec(v_x_3831_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3948_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_array_get(v___x_3828_, v_embeds_3829_, v_fst_3834_);
lean_dec(v_fst_3834_);
switch(lean_obj_tag(v___x_3839_))
{
case 0:
{
lean_object* v_ctx_3840_; lean_object* v_infos_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3852_; 
lean_del_object(v___x_3837_);
lean_dec(v_snd_3835_);
lean_dec(v_indent_3830_);
lean_dec_ref(v_embeds_3829_);
v_ctx_3840_ = lean_ctor_get(v___x_3839_, 0);
v_infos_3841_ = lean_ctor_get(v___x_3839_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3843_ = v___x_3839_;
v_isShared_3844_ = v_isSharedCheck_3852_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_infos_3841_);
lean_inc(v_ctx_3840_);
lean_dec(v___x_3839_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3852_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3845_ = l_Lean_Widget_tagCodeInfos(v_ctx_3840_, v_infos_3841_, v_tt_3832_);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
v___x_3847_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 2);
lean_ctor_set(v___x_3843_, 1, v___x_3847_);
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3849_ = v___x_3843_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
}
}
case 1:
{
lean_object* v_ctx_3853_; lean_object* v_lctx_3854_; lean_object* v_g_3855_; lean_object* v___f_3856_; lean_object* v___x_3857_; 
lean_del_object(v___x_3837_);
lean_dec(v_snd_3835_);
lean_dec_ref(v_tt_3832_);
lean_dec(v_indent_3830_);
lean_dec_ref(v_embeds_3829_);
v_ctx_3853_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref(v_ctx_3853_);
v_lctx_3854_ = lean_ctor_get(v___x_3839_, 1);
lean_inc_ref(v_lctx_3854_);
v_g_3855_ = lean_ctor_get(v___x_3839_, 2);
lean_inc(v_g_3855_);
lean_dec_ref_known(v___x_3839_, 3);
v___f_3856_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3856_, 0, v_g_3855_);
v___x_3857_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_3853_, v_lctx_3854_, v___f_3856_);
return v___x_3857_;
}
case 2:
{
lean_object* v_wi_3858_; lean_object* v_alt_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v_tt_3832_);
lean_dec(v_indent_3830_);
v_wi_3858_ = lean_ctor_get(v___x_3839_, 0);
v_alt_3859_ = lean_ctor_get(v___x_3839_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3861_ = v___x_3839_;
v_isShared_3862_ = v_isSharedCheck_3879_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_alt_3859_);
lean_inc(v_wi_3858_);
lean_dec(v___x_3839_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3879_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; 
v___x_3863_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3829_, v_alt_3859_, v_snd_3835_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3878_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3878_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3878_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v_a_3864_);
v___x_3869_ = v___x_3861_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_wi_3858_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3870_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 2);
lean_ctor_set(v___x_3837_, 1, v___x_3870_);
lean_ctor_set(v___x_3837_, 0, v___x_3869_);
v___x_3872_ = v___x_3837_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3872_);
v___x_3874_ = v___x_3866_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
else
{
lean_del_object(v___x_3861_);
lean_dec_ref(v_wi_3858_);
lean_del_object(v___x_3837_);
return v___x_3863_;
}
}
}
case 3:
{
lean_object* v_cls_3880_; lean_object* v_msg_3881_; uint8_t v_collapsed_3882_; lean_object* v_children_3883_; lean_object* v_col_3884_; lean_object* v_children_3886_; 
lean_dec_ref(v_tt_3832_);
v_cls_3880_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_cls_3880_);
v_msg_3881_ = lean_ctor_get(v___x_3839_, 1);
lean_inc(v_msg_3881_);
v_collapsed_3882_ = lean_ctor_get_uint8(v___x_3839_, sizeof(void*)*3);
v_children_3883_ = lean_ctor_get(v___x_3839_, 2);
lean_inc_ref(v_children_3883_);
lean_dec_ref_known(v___x_3839_, 3);
v_col_3884_ = lean_nat_add(v_indent_3830_, v_snd_3835_);
lean_dec(v_snd_3835_);
if (lean_obj_tag(v_children_3883_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3920_; 
v_a_3901_ = lean_ctor_get(v_children_3883_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_children_3883_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3903_ = v_children_3883_;
v_isShared_3904_ = v_isSharedCheck_3920_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v_children_3883_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3920_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
size_t v_sz_3905_; size_t v___x_3906_; lean_object* v___x_3907_; 
v_sz_3905_ = lean_array_size(v_a_3901_);
v___x_3906_ = ((size_t)0ULL);
lean_inc_ref(v_embeds_3829_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3884_, v_embeds_3829_, v_sz_3905_, v___x_3906_, v_a_3901_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v_a_3908_);
v___x_3910_ = v___x_3903_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
v_children_3886_ = v___x_3910_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_del_object(v___x_3903_);
lean_dec(v_col_3884_);
lean_dec(v_msg_3881_);
lean_dec(v_cls_3880_);
lean_del_object(v___x_3837_);
lean_dec(v_indent_3830_);
lean_dec_ref(v_embeds_3829_);
v_a_3912_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3907_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3907_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3944_; 
v_a_3921_ = lean_ctor_get(v_children_3883_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_children_3883_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3923_ = v_children_3883_;
v_isShared_3924_ = v_isSharedCheck_3944_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v_children_3883_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3944_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
size_t v_sz_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v_sz_3925_ = lean_array_size(v_a_3921_);
v___x_3926_ = ((size_t)0ULL);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_3925_, v___x_3926_, v_a_3921_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3929_ = lean_unsigned_to_nat(2u);
v___x_3930_ = lean_nat_add(v_col_3884_, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v_a_3928_);
v___x_3932_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_3931_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3932_);
v___x_3934_ = v___x_3923_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
v_children_3886_ = v___x_3934_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_del_object(v___x_3923_);
lean_dec(v_col_3884_);
lean_dec(v_msg_3881_);
lean_dec(v_cls_3880_);
lean_del_object(v___x_3837_);
lean_dec(v_indent_3830_);
lean_dec_ref(v_embeds_3829_);
v_a_3936_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3927_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3927_);
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
}
v___jp_3885_:
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3829_, v_msg_3881_, v_col_3884_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3900_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3890_ = v___x_3887_;
v_isShared_3891_ = v_isSharedCheck_3900_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3900_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3892_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_3892_, 0, v_indent_3830_);
lean_ctor_set(v___x_3892_, 1, v_cls_3880_);
lean_ctor_set(v___x_3892_, 2, v_a_3888_);
lean_ctor_set(v___x_3892_, 3, v_children_3886_);
lean_ctor_set_uint8(v___x_3892_, sizeof(void*)*4, v_collapsed_3882_);
v___x_3893_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 2);
lean_ctor_set(v___x_3837_, 1, v___x_3893_);
lean_ctor_set(v___x_3837_, 0, v___x_3892_);
v___x_3895_ = v___x_3837_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3895_);
v___x_3897_ = v___x_3890_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
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
else
{
lean_dec_ref(v_children_3886_);
lean_dec(v_cls_3880_);
lean_del_object(v___x_3837_);
lean_dec(v_indent_3830_);
return v___x_3887_;
}
}
}
default: 
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_del_object(v___x_3837_);
lean_dec(v_snd_3835_);
lean_dec(v_indent_3830_);
lean_dec_ref(v_embeds_3829_);
v___x_3945_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3832_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3828_ = stack[0].m_obj;
lean_object* v_embeds_3829_ = stack[1].m_obj;
lean_object* v_indent_3830_ = stack[2].m_obj;
lean_object* v_x_3831_ = stack[3].m_obj;
lean_object* v_tt_3832_ = stack[4].m_obj;
lean_object* v_res_3949_;
v_res_3949_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(v___x_3828_, v_embeds_3829_, v_indent_3830_, v_x_3831_, v_tt_3832_);
stack->m_obj
 = v_res_3949_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed(lean_object* v___x_3950_, lean_object* v_embeds_3951_, lean_object* v_indent_3952_, lean_object* v_x_3953_, lean_object* v_tt_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(v___x_3950_, v_embeds_3951_, v_indent_3952_, v_x_3953_, v_tt_3954_);
lean_dec(v___x_3950_);
return v_res_3956_;
}
}
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(lean_object* v_embeds_3957_, lean_object* v_fmt_3958_, lean_object* v_indent_3959_){
_start:
{
lean_object* v___x_3961_; lean_object* v___f_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = l_Lean_Widget_instInhabitedEmbedFmt_default;
lean_inc(v_indent_3959_);
v___f_3962_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3962_, 0, v___x_3961_);
lean_closure_set(v___f_3962_, 1, v_embeds_3957_);
lean_closure_set(v___f_3962_, 2, v_indent_3959_);
v___x_3963_ = l_Std_Format_defWidth;
v___x_3964_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_3958_, v_indent_3959_, v___x_3963_);
v___x_3965_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v___f_3962_, v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT void l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_0interp(lean_interpreter_value* stack)
{
lean_object* v_embeds_3957_ = stack[0].m_obj;
lean_object* v_fmt_3958_ = stack[1].m_obj;
lean_object* v_indent_3959_ = stack[2].m_obj;
lean_object* v_res_3966_;
v_res_3966_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3957_, v_fmt_3958_, v_indent_3959_);
stack->m_obj
 = v_res_3966_;
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___boxed(lean_object* v_embeds_3967_, lean_object* v_fmt_3968_, lean_object* v_indent_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3967_, v_fmt_3968_, v_indent_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object* v_col_3972_, lean_object* v_embeds_3973_, lean_object* v_sz_3974_, lean_object* v_i_3975_, lean_object* v_bs_3976_, lean_object* v___y_3977_){
_start:
{
size_t v_sz_boxed_3978_; size_t v_i_boxed_3979_; lean_object* v_res_3980_; 
v_sz_boxed_3978_ = lean_unbox_usize(v_sz_3974_);
lean_dec(v_sz_3974_);
v_i_boxed_3979_ = lean_unbox_usize(v_i_3975_);
lean_dec(v_i_3975_);
v_res_3980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3972_, v_embeds_3973_, v_sz_boxed_3978_, v_i_boxed_3979_, v_bs_3976_);
lean_dec(v_col_3972_);
return v_res_3980_;
}
}
lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object* v_00_u03b1_3981_, lean_object* v_00_u03b2_3982_, lean_object* v_f_3983_, lean_object* v_x_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3983_, v_x_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT void l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3983_ = stack[2].m_obj;
lean_object* v_x_3984_ = stack[3].m_obj;
lean_object* v_res_3987_;
v_res_3987_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_box(0), lean_box(0), v_f_3983_, v_x_3984_);
stack->m_obj
 = v_res_3987_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_00_u03b2_3989_, lean_object* v_f_3990_, lean_object* v_x_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(v_00_u03b1_3988_, v_00_u03b2_3989_, v_f_3990_, v_x_3991_);
return v_res_3993_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object* v_00_u03b1_3994_, lean_object* v_00_u03b2_3995_, lean_object* v_f_3996_, size_t v_sz_3997_, size_t v_i_3998_, lean_object* v_bs_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3996_, v_sz_3997_, v_i_3998_, v_bs_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3996_ = stack[2].m_obj;
size_t v_sz_3997_ = stack[3].m_num;
size_t v_i_3998_ = stack[4].m_num;
lean_object* v_bs_3999_ = stack[5].m_obj;
lean_object* v_res_4002_;
v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_box(0), lean_box(0), v_f_3996_, v_sz_3997_, v_i_3998_, v_bs_3999_);
stack->m_obj
 = v_res_4002_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4003_, lean_object* v_00_u03b2_4004_, lean_object* v_f_4005_, lean_object* v_sz_4006_, lean_object* v_i_4007_, lean_object* v_bs_4008_, lean_object* v___y_4009_){
_start:
{
size_t v_sz_boxed_4010_; size_t v_i_boxed_4011_; lean_object* v_res_4012_; 
v_sz_boxed_4010_ = lean_unbox_usize(v_sz_4006_);
lean_dec(v_sz_4006_);
v_i_boxed_4011_ = lean_unbox_usize(v_i_4007_);
lean_dec(v_i_4007_);
v_res_4012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(v_00_u03b1_4003_, v_00_u03b2_4004_, v_f_4005_, v_sz_boxed_4010_, v_i_boxed_4011_, v_bs_4008_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object* v_x_4013_, lean_object* v_tt_4014_){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_4014_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object* v_x_4017_, lean_object* v_tt_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Widget_msgToInteractive___lam__0(v_x_4017_, v_tt_4018_);
lean_dec_ref(v_x_4017_);
return v_res_4019_;
}
}
lean_object* l_Lean_Widget_msgToInteractive(lean_object* v_msgData_4021_, uint8_t v_hasWidgets_4022_, lean_object* v_indent_4023_){
_start:
{
if (v_hasWidgets_4022_ == 0)
{
lean_object* v___f_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_dec(v_indent_4023_);
v___f_4025_ = ((lean_object*)(l_Lean_Widget_msgToInteractive___closed__0));
v___x_4026_ = lean_box(0);
v___x_4027_ = l_Lean_MessageData_format(v_msgData_4021_, v___x_4026_);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = l_Std_Format_defWidth;
v___x_4030_ = l_Lean_Widget_TaggedText_prettyTagged(v___x_4027_, v___x_4028_, v___x_4029_);
v___x_4031_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_4025_, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
else
{
lean_object* v___x_4033_; 
v___x_4033_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_4021_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v_fst_4035_; lean_object* v_snd_4036_; lean_object* v___x_4037_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v_fst_4035_ = lean_ctor_get(v_a_4034_, 0);
lean_inc(v_fst_4035_);
v_snd_4036_ = lean_ctor_get(v_a_4034_, 1);
lean_inc(v_snd_4036_);
lean_dec(v_a_4034_);
v___x_4037_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_snd_4036_, v_fst_4035_, v_indent_4023_);
return v___x_4037_;
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_indent_4023_);
v_a_4038_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4033_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4033_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_msgToInteractive_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4021_ = stack[0].m_obj;
uint8_t v_hasWidgets_4022_ = stack[1].m_num;
lean_object* v_indent_4023_ = stack[2].m_obj;
lean_object* v_res_4046_;
v_res_4046_ = l_Lean_Widget_msgToInteractive(v_msgData_4021_, v_hasWidgets_4022_, v_indent_4023_);
stack->m_obj
 = v_res_4046_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object* v_msgData_4047_, lean_object* v_hasWidgets_4048_, lean_object* v_indent_4049_, lean_object* v_a_4050_){
_start:
{
uint8_t v_hasWidgets_boxed_4051_; lean_object* v_res_4052_; 
v_hasWidgets_boxed_4051_ = lean_unbox(v_hasWidgets_4048_);
v_res_4052_ = l_Lean_Widget_msgToInteractive(v_msgData_4047_, v_hasWidgets_boxed_4051_, v_indent_4049_);
return v_res_4052_;
}
}
uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object* v_x_4058_){
_start:
{
lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4059_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2));
v___x_4060_ = lean_name_eq(v_x_4058_, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT void l_Lean_Widget_msgToInteractiveDiagnostic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4058_ = stack[0].m_obj;
uint8_t v_res_4061_;
v_res_4061_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(v_x_4058_);
stack->m_num = v_res_4061_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object* v_x_4062_){
_start:
{
uint8_t v_res_4063_; lean_object* v_r_4064_; 
v_res_4063_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(v_x_4062_);
lean_dec(v_x_4062_);
v_r_4064_ = lean_box(v_res_4063_);
return v_r_4064_;
}
}
uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object* v_x_4068_){
_start:
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1));
v___x_4070_ = lean_name_eq(v_x_4068_, v___x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT void l_Lean_Widget_msgToInteractiveDiagnostic___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4068_ = stack[0].m_obj;
uint8_t v_res_4071_;
v_res_4071_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(v_x_4068_);
stack->m_num = v_res_4071_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object* v_x_4072_){
_start:
{
uint8_t v_res_4073_; lean_object* v_r_4074_; 
v_res_4073_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(v_x_4072_);
lean_dec(v_x_4072_);
v_r_4074_ = lean_box(v_res_4073_);
return v_r_4074_;
}
}
lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object* v_text_4113_, lean_object* v_m_4114_, uint8_t v_hasWidgets_4115_){
_start:
{
lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v_pos_4130_; lean_object* v_endPos_4131_; uint8_t v_keepFullRange_4132_; uint8_t v_severity_4133_; uint8_t v_isSilent_4134_; lean_object* v_data_4135_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; uint8_t v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; uint8_t v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___f_4184_; lean_object* v___f_4185_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; uint8_t v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___y_4214_; lean_object* v_low_4220_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4230_; 
v_pos_4130_ = lean_ctor_get(v_m_4114_, 1);
lean_inc_ref_n(v_pos_4130_, 2);
v_endPos_4131_ = lean_ctor_get(v_m_4114_, 2);
lean_inc(v_endPos_4131_);
v_keepFullRange_4132_ = lean_ctor_get_uint8(v_m_4114_, sizeof(void*)*5);
v_severity_4133_ = lean_ctor_get_uint8(v_m_4114_, sizeof(void*)*5 + 1);
v_isSilent_4134_ = lean_ctor_get_uint8(v_m_4114_, sizeof(void*)*5 + 2);
v_data_4135_ = lean_ctor_get(v_m_4114_, 4);
lean_inc(v_data_4135_);
lean_dec_ref(v_m_4114_);
v___f_4184_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__2));
v___f_4185_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__3));
lean_inc_ref(v_text_4113_);
v_low_4220_ = l_Lean_FileMap_leanPosToLspPos(v_text_4113_, v_pos_4130_);
if (lean_obj_tag(v_endPos_4131_) == 0)
{
lean_inc_ref(v_pos_4130_);
v___y_4230_ = v_pos_4130_;
goto v___jp_4229_;
}
else
{
lean_object* v_val_4252_; 
v_val_4252_ = lean_ctor_get(v_endPos_4131_, 0);
lean_inc(v_val_4252_);
v___y_4230_ = v_val_4252_;
goto v___jp_4229_;
}
v___jp_4117_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___y_4120_);
v___x_4128_ = lean_box(0);
lean_inc(v___y_4119_);
lean_inc(v___y_4123_);
lean_inc(v___y_4124_);
lean_inc(v___y_4121_);
v___x_4129_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4129_, 0, v___y_4122_);
lean_ctor_set(v___x_4129_, 1, v___x_4127_);
lean_ctor_set(v___x_4129_, 2, v___y_4118_);
lean_ctor_set(v___x_4129_, 3, v___y_4121_);
lean_ctor_set(v___x_4129_, 4, v___y_4126_);
lean_ctor_set(v___x_4129_, 5, v___y_4124_);
lean_ctor_set(v___x_4129_, 6, v___y_4125_);
lean_ctor_set(v___x_4129_, 7, v___y_4123_);
lean_ctor_set(v___x_4129_, 8, v___y_4119_);
lean_ctor_set(v___x_4129_, 9, v___x_4128_);
lean_ctor_set(v___x_4129_, 10, v___x_4128_);
return v___x_4129_;
}
v___jp_4136_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = l_Lean_MessageData_kind(v_data_4135_);
lean_dec(v_data_4135_);
v___x_4147_ = l_Lean_errorNameOfKind_x3f(v___x_4146_);
lean_dec(v___x_4146_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_box(0);
v___y_4118_ = v___y_4137_;
v___y_4119_ = v___y_4139_;
v___y_4120_ = v___y_4138_;
v___y_4121_ = v___y_4141_;
v___y_4122_ = v___y_4140_;
v___y_4123_ = v___y_4142_;
v___y_4124_ = v___y_4144_;
v___y_4125_ = v___y_4145_;
v___y_4126_ = v___x_4148_;
goto v___jp_4117_;
}
else
{
lean_object* v_val_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4158_; 
v_val_4149_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4151_ = v___x_4147_;
v_isShared_4152_ = v_isSharedCheck_4158_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_val_4149_);
lean_dec(v___x_4147_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4158_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4153_ = l_Lean_Name_toString(v_val_4149_, v___y_4143_);
v___x_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4154_);
v___x_4156_ = v___x_4151_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
v___y_4118_ = v___y_4137_;
v___y_4119_ = v___y_4139_;
v___y_4120_ = v___y_4138_;
v___y_4121_ = v___y_4141_;
v___y_4122_ = v___y_4140_;
v___y_4123_ = v___y_4142_;
v___y_4124_ = v___y_4144_;
v___y_4125_ = v___y_4145_;
v___y_4126_ = v___x_4156_;
goto v___jp_4117_;
}
}
}
}
v___jp_4159_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = lean_unsigned_to_nat(0u);
lean_inc(v_data_4135_);
v___x_4169_ = l_Lean_Widget_msgToInteractive(v_data_4135_, v_hasWidgets_4115_, v___x_4168_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4169_, 1);
v___y_4137_ = v___y_4160_;
v___y_4138_ = v___y_4161_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4162_;
v___y_4141_ = v___y_4163_;
v___y_4142_ = v___y_4164_;
v___y_4143_ = v___y_4165_;
v___y_4144_ = v___y_4166_;
v___y_4145_ = v_a_4170_;
goto v___jp_4136_;
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4183_; 
v_a_4171_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4173_ = v___x_4169_;
v_isShared_4174_ = v_isSharedCheck_4183_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4169_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4183_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4175_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__0));
v___x_4176_ = lean_io_error_to_string(v_a_4171_);
v___x_4177_ = lean_string_append(v___x_4175_, v___x_4176_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__1));
v___x_4179_ = lean_string_append(v___x_4177_, v___x_4178_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set_tag(v___x_4173_, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4179_);
v___x_4181_ = v___x_4173_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
v___y_4137_ = v___y_4160_;
v___y_4138_ = v___y_4161_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4162_;
v___y_4141_ = v___y_4163_;
v___y_4142_ = v___y_4164_;
v___y_4143_ = v___y_4165_;
v___y_4144_ = v___y_4166_;
v___y_4145_ = v___x_4181_;
goto v___jp_4136_;
}
}
}
}
v___jp_4186_:
{
uint8_t v___x_4194_; 
lean_inc(v_data_4135_);
v___x_4194_ = l_Lean_MessageData_hasTag(v___f_4184_, v_data_4135_);
if (v___x_4194_ == 0)
{
uint8_t v___x_4195_; 
lean_inc(v_data_4135_);
v___x_4195_ = l_Lean_MessageData_hasTag(v___f_4185_, v_data_4135_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_box(0);
v___y_4160_ = v___y_4187_;
v___y_4161_ = v___y_4188_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4189_;
v___y_4164_ = v___y_4193_;
v___y_4165_ = v___y_4191_;
v___y_4166_ = v___y_4192_;
v___y_4167_ = v___x_4196_;
goto v___jp_4159_;
}
else
{
lean_object* v___x_4197_; 
v___x_4197_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__5));
v___y_4160_ = v___y_4187_;
v___y_4161_ = v___y_4188_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4189_;
v___y_4164_ = v___y_4193_;
v___y_4165_ = v___y_4191_;
v___y_4166_ = v___y_4192_;
v___y_4167_ = v___x_4197_;
goto v___jp_4159_;
}
}
else
{
lean_object* v___x_4198_; 
v___x_4198_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__7));
v___y_4160_ = v___y_4187_;
v___y_4161_ = v___y_4188_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4189_;
v___y_4164_ = v___y_4193_;
v___y_4165_ = v___y_4191_;
v___y_4166_ = v___y_4192_;
v___y_4167_ = v___x_4198_;
goto v___jp_4159_;
}
}
v___jp_4199_:
{
lean_object* v_source_x3f_4205_; uint8_t v___x_4206_; 
v_source_x3f_4205_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__9));
lean_inc(v_data_4135_);
v___x_4206_ = l_Lean_MessageData_isDeprecationWarning(v_data_4135_);
if (v___x_4206_ == 0)
{
uint8_t v___x_4207_; 
lean_inc(v_data_4135_);
v___x_4207_ = l_Lean_MessageData_isUnusedVariableWarning(v_data_4135_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_box(0);
v___y_4187_ = v___y_4200_;
v___y_4188_ = v___y_4201_;
v___y_4189_ = v___y_4204_;
v___y_4190_ = v___y_4202_;
v___y_4191_ = v___y_4203_;
v___y_4192_ = v_source_x3f_4205_;
v___y_4193_ = v___x_4208_;
goto v___jp_4186_;
}
else
{
lean_object* v___x_4209_; 
v___x_4209_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__11));
v___y_4187_ = v___y_4200_;
v___y_4188_ = v___y_4201_;
v___y_4189_ = v___y_4204_;
v___y_4190_ = v___y_4202_;
v___y_4191_ = v___y_4203_;
v___y_4192_ = v_source_x3f_4205_;
v___y_4193_ = v___x_4209_;
goto v___jp_4186_;
}
}
else
{
lean_object* v___x_4210_; 
v___x_4210_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__13));
v___y_4187_ = v___y_4200_;
v___y_4188_ = v___y_4201_;
v___y_4189_ = v___y_4204_;
v___y_4190_ = v___y_4202_;
v___y_4191_ = v___y_4203_;
v___y_4192_ = v_source_x3f_4205_;
v___y_4193_ = v___x_4210_;
goto v___jp_4186_;
}
}
v___jp_4211_:
{
lean_object* v___x_4215_; lean_object* v_severity_x3f_4216_; uint8_t v___x_4217_; 
v___x_4215_ = lean_box(v___y_4214_);
v_severity_x3f_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_severity_x3f_4216_, 0, v___x_4215_);
v___x_4217_ = 1;
if (v_isSilent_4134_ == 0)
{
lean_object* v___x_4218_; 
v___x_4218_ = lean_box(0);
v___y_4200_ = v_severity_x3f_4216_;
v___y_4201_ = v___y_4212_;
v___y_4202_ = v___y_4213_;
v___y_4203_ = v___x_4217_;
v___y_4204_ = v___x_4218_;
goto v___jp_4199_;
}
else
{
lean_object* v___x_4219_; 
v___x_4219_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__14));
v___y_4200_ = v_severity_x3f_4216_;
v___y_4201_ = v___y_4212_;
v___y_4202_ = v___y_4213_;
v___y_4203_ = v___x_4217_;
v___y_4204_ = v___x_4219_;
goto v___jp_4199_;
}
}
v___jp_4221_:
{
lean_object* v_range_4224_; lean_object* v_fullRange_4225_; 
lean_inc_ref(v_low_4220_);
v_range_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_4224_, 0, v_low_4220_);
lean_ctor_set(v_range_4224_, 1, v___y_4223_);
v_fullRange_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_fullRange_4225_, 0, v_low_4220_);
lean_ctor_set(v_fullRange_4225_, 1, v___y_4222_);
switch(v_severity_4133_)
{
case 0:
{
uint8_t v___x_4226_; 
v___x_4226_ = 2;
v___y_4212_ = v_fullRange_4225_;
v___y_4213_ = v_range_4224_;
v___y_4214_ = v___x_4226_;
goto v___jp_4211_;
}
case 1:
{
uint8_t v___x_4227_; 
v___x_4227_ = 1;
v___y_4212_ = v_fullRange_4225_;
v___y_4213_ = v_range_4224_;
v___y_4214_ = v___x_4227_;
goto v___jp_4211_;
}
default: 
{
uint8_t v___x_4228_; 
v___x_4228_ = 0;
v___y_4212_ = v_fullRange_4225_;
v___y_4213_ = v_range_4224_;
v___y_4214_ = v___x_4228_;
goto v___jp_4211_;
}
}
}
v___jp_4229_:
{
lean_object* v_fullHigh_4231_; 
lean_inc_ref(v_text_4113_);
v_fullHigh_4231_ = l_Lean_FileMap_leanPosToLspPos(v_text_4113_, v___y_4230_);
if (lean_obj_tag(v_endPos_4131_) == 0)
{
lean_dec_ref(v_pos_4130_);
lean_dec_ref(v_text_4113_);
lean_inc_ref(v_low_4220_);
v___y_4222_ = v_fullHigh_4231_;
v___y_4223_ = v_low_4220_;
goto v___jp_4221_;
}
else
{
if (v_keepFullRange_4132_ == 0)
{
lean_object* v_val_4232_; lean_object* v_line_4233_; lean_object* v_line_4234_; uint8_t v___x_4235_; 
v_val_4232_ = lean_ctor_get(v_endPos_4131_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v_endPos_4131_, 1);
v_line_4233_ = lean_ctor_get(v_pos_4130_, 0);
lean_inc(v_line_4233_);
lean_dec_ref(v_pos_4130_);
v_line_4234_ = lean_ctor_get(v_val_4232_, 0);
v___x_4235_ = lean_nat_dec_lt(v_line_4233_, v_line_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; 
lean_dec(v_line_4233_);
v___x_4236_ = l_Lean_FileMap_leanPosToLspPos(v_text_4113_, v_val_4232_);
v___y_4222_ = v_fullHigh_4231_;
v___y_4223_ = v___x_4236_;
goto v___jp_4221_;
}
else
{
lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4247_; 
v_isSharedCheck_4247_ = !lean_is_exclusive(v_val_4232_);
if (v_isSharedCheck_4247_ == 0)
{
lean_object* v_unused_4248_; lean_object* v_unused_4249_; 
v_unused_4248_ = lean_ctor_get(v_val_4232_, 1);
lean_dec(v_unused_4248_);
v_unused_4249_ = lean_ctor_get(v_val_4232_, 0);
lean_dec(v_unused_4249_);
v___x_4238_ = v_val_4232_;
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
else
{
lean_dec(v_val_4232_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4240_ = lean_unsigned_to_nat(1u);
v___x_4241_ = lean_nat_add(v_line_4233_, v___x_4240_);
lean_dec(v_line_4233_);
v___x_4242_ = lean_unsigned_to_nat(0u);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 1, v___x_4242_);
lean_ctor_set(v___x_4238_, 0, v___x_4241_);
v___x_4244_ = v___x_4238_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_FileMap_leanPosToLspPos(v_text_4113_, v___x_4244_);
v___y_4222_ = v_fullHigh_4231_;
v___y_4223_ = v___x_4245_;
goto v___jp_4221_;
}
}
}
}
else
{
lean_object* v_val_4250_; lean_object* v___x_4251_; 
lean_dec_ref(v_pos_4130_);
v_val_4250_ = lean_ctor_get(v_endPos_4131_, 0);
lean_inc(v_val_4250_);
lean_dec_ref_known(v_endPos_4131_, 1);
v___x_4251_ = l_Lean_FileMap_leanPosToLspPos(v_text_4113_, v_val_4250_);
v___y_4222_ = v_fullHigh_4231_;
v___y_4223_ = v___x_4251_;
goto v___jp_4221_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Widget_msgToInteractiveDiagnostic_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_4113_ = stack[0].m_obj;
lean_object* v_m_4114_ = stack[1].m_obj;
uint8_t v_hasWidgets_4115_ = stack[2].m_num;
lean_object* v_res_4253_;
v_res_4253_ = l_Lean_Widget_msgToInteractiveDiagnostic(v_text_4113_, v_m_4114_, v_hasWidgets_4115_);
stack->m_obj
 = v_res_4253_;
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object* v_text_4254_, lean_object* v_m_4255_, lean_object* v_hasWidgets_4256_, lean_object* v_a_4257_){
_start:
{
uint8_t v_hasWidgets_boxed_4258_; lean_object* v_res_4259_; 
v_hasWidgets_boxed_4258_ = lean_unbox(v_hasWidgets_4256_);
v_res_4259_ = l_Lean_Widget_msgToInteractiveDiagnostic(v_text_4254_, v_m_4255_, v_hasWidgets_boxed_4258_);
return v_res_4259_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_UnusedVariables(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Widget_instInhabitedMsgEmbed_default = _init_l_Lean_Widget_instInhabitedMsgEmbed_default();
lean_mark_persistent(l_Lean_Widget_instInhabitedMsgEmbed_default);
l_Lean_Widget_instInhabitedMsgEmbed = _init_l_Lean_Widget_instInhabitedMsgEmbed();
lean_mark_persistent(l_Lean_Widget_instInhabitedMsgEmbed);
l_Lean_Widget_instInhabitedEmbedFmt_default = _init_l_Lean_Widget_instInhabitedEmbedFmt_default();
lean_mark_persistent(l_Lean_Widget_instInhabitedEmbedFmt_default);
l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt = _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt();
lean_mark_persistent(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_UnusedVariables(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_InteractiveDiagnostic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Widget_InteractiveDiagnostic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Widget_InteractiveDiagnostic(builtin);
}
#ifdef __cplusplus
}
#endif
