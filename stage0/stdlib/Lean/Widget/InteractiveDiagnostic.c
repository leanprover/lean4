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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_){
_start:
{
size_t v_sz_boxed_721_; size_t v_i_boxed_722_; lean_object* v_res_723_; 
v_sz_boxed_721_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_722_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_boxed_721_, v_i_boxed_722_, v_bs_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object* v_a_724_){
_start:
{
size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_sz_725_ = lean_array_size(v_a_724_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_725_, v___x_726_, v_a_724_);
v___x_728_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object* v_x_732_){
_start:
{
switch(lean_obj_tag(v_x_732_))
{
case 0:
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_745_; 
v_a_733_ = lean_ctor_get(v_x_732_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_735_ = v_x_732_;
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v_x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 3);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_733_);
v___x_739_ = v_reuseFailAlloc_744_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_box(0);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_Json_mkObj(v___x_742_);
lean_dec_ref_known(v___x_742_, 2);
return v___x_743_;
}
}
}
case 1:
{
lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_746_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref(v_a_746_);
lean_dec_ref_known(v_x_732_, 1);
v___x_747_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_748_ = l_Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(v_a_746_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_Json_mkObj(v___x_751_);
lean_dec_ref_known(v___x_751_, 2);
return v___x_752_;
}
default: 
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_771_; 
v_a_753_ = lean_ctor_get(v_x_732_, 0);
v_a_754_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_771_ == 0)
{
v___x_756_ = v_x_732_;
v_isShared_757_ = v_isSharedCheck_771_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v_x_732_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_771_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_758_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_759_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_a_754_);
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_mk_empty_array_with_capacity(v___x_760_);
v___x_762_ = lean_array_push(v___x_761_, v_a_753_);
v___x_763_ = lean_array_push(v___x_762_, v___x_759_);
v___x_764_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 0);
lean_ctor_set(v___x_756_, 1, v___x_764_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_766_ = v___x_756_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_Json_mkObj(v___x_768_);
lean_dec_ref_known(v___x_768_, 2);
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t v_sz_772_, size_t v_i_773_, lean_object* v_bs_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_775_ == 0)
{
return v_bs_774_;
}
else
{
lean_object* v_v_776_; lean_object* v___x_777_; lean_object* v_bs_x27_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v_v_776_ = lean_array_uget(v_bs_774_, v_i_773_);
v___x_777_ = lean_unsigned_to_nat(0u);
v_bs_x27_778_ = lean_array_uset(v_bs_774_, v_i_773_, v___x_777_);
v___x_779_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_v_776_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_773_, v___x_780_);
v___x_782_ = lean_array_uset(v_bs_x27_778_, v_i_773_, v___x_779_);
v_i_773_ = v___x_781_;
v_bs_774_ = v___x_782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object* v_a_784_){
_start:
{
size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_sz_785_ = lean_array_size(v_a_784_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_785_, v___x_786_, v_a_784_);
v___x_788_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object* v_sz_789_, lean_object* v_i_790_, lean_object* v_bs_791_){
_start:
{
size_t v_sz_boxed_792_; size_t v_i_boxed_793_; lean_object* v_res_794_; 
v_sz_boxed_792_ = lean_unbox_usize(v_sz_789_);
lean_dec(v_sz_789_);
v_i_boxed_793_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_boxed_792_, v_i_boxed_793_, v_bs_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(lean_object* v_f_795_, lean_object* v_x_796_, lean_object* v___y_797_){
_start:
{
switch(lean_obj_tag(v_x_796_))
{
case 0:
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_f_795_);
v_a_798_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v_x_796_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v_x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___y_797_);
return v___x_804_;
}
}
}
case 1:
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_826_; 
v_a_807_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_826_ == 0)
{
v___x_809_ = v_x_796_;
v_isShared_810_ = v_isSharedCheck_826_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v_x_796_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_826_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_825_; 
v_sz_811_ = lean_array_size(v_a_807_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_795_, v_sz_811_, v___x_812_, v_a_807_, v___y_797_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
v_snd_815_ = lean_ctor_get(v___x_813_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_825_ == 0)
{
v___x_817_ = v___x_813_;
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v___x_813_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v_fst_814_);
v___x_820_ = v___x_809_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_fst_814_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_815_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
default: 
{
lean_object* v_a_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_a_827_ = lean_ctor_get(v_x_796_, 0);
v_a_828_ = lean_ctor_get(v_x_796_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v_x_796_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_inc(v_a_827_);
lean_dec(v_x_796_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_835_; lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
lean_inc_ref(v_f_795_);
v___x_832_ = lean_apply_2(v_f_795_, v_a_827_, v___y_797_);
v_fst_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_fst_833_);
v_snd_834_ = lean_ctor_get(v___x_832_, 1);
lean_inc(v_snd_834_);
lean_dec_ref(v___x_832_);
v___x_835_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_795_, v_a_828_, v_snd_834_);
v_fst_836_ = lean_ctor_get(v___x_835_, 0);
v_snd_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_847_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_fst_836_);
lean_ctor_set(v___x_830_, 0, v_fst_833_);
v___x_842_ = v___x_830_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_fst_833_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_fst_836_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_snd_837_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(lean_object* v_f_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_bs_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v_f_849_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_bs_852_);
lean_ctor_set(v___x_855_, 1, v___y_853_);
return v___x_855_;
}
else
{
lean_object* v_v_856_; lean_object* v___x_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_860_; lean_object* v_bs_x27_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v_v_856_ = lean_array_uget_borrowed(v_bs_852_, v_i_851_);
lean_inc(v_v_856_);
lean_inc_ref(v_f_849_);
v___x_857_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_849_, v_v_856_, v___y_853_);
v_fst_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_snd_859_);
lean_dec_ref(v___x_857_);
v___x_860_ = lean_unsigned_to_nat(0u);
v_bs_x27_861_ = lean_array_uset(v_bs_852_, v_i_851_, v___x_860_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_851_, v___x_862_);
v___x_864_ = lean_array_uset(v_bs_x27_861_, v_i_851_, v_fst_858_);
v_i_851_ = v___x_863_;
v_bs_852_ = v___x_864_;
v___y_853_ = v_snd_859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg___boxed(lean_object* v_f_866_, lean_object* v_sz_867_, lean_object* v_i_868_, lean_object* v_bs_869_, lean_object* v___y_870_){
_start:
{
size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v_sz_boxed_871_ = lean_unbox_usize(v_sz_867_);
lean_dec(v_sz_867_);
v_i_boxed_872_ = lean_unbox_usize(v_i_868_);
lean_dec(v_i_868_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_866_, v_sz_boxed_871_, v_i_boxed_872_, v_bs_869_, v___y_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(lean_object* v_x_875_, lean_object* v_a_876_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_898_; 
v_a_877_ = lean_ctor_get(v_x_875_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_898_ == 0)
{
v___x_879_ = v_x_875_;
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v_x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_sz_881_ = lean_array_size(v_a_877_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_881_, v___x_882_, v_a_877_, v_a_876_);
v_fst_884_ = lean_ctor_get(v___x_883_, 0);
v_snd_885_ = lean_ctor_get(v___x_883_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_inc(v_fst_884_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(v_fst_884_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_889_);
v___x_891_ = v___x_879_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_896_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_891_);
lean_dec_ref(v___x_891_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_892_);
v___x_894_ = v___x_887_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_885_);
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
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_918_; 
v_a_899_ = lean_ctor_get(v_x_875_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_918_ == 0)
{
v___x_901_ = v_x_875_;
v_isShared_902_ = v_isSharedCheck_918_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v_x_875_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_918_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v___x_903_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_904_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_903_, v_a_899_, v_a_876_);
lean_dec(v_a_899_);
v_fst_905_ = lean_ctor_get(v___x_904_, 0);
v_snd_906_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_917_ == 0)
{
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_fst_905_);
v___x_911_ = v___x_901_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_905_);
v___x_911_ = v_reuseFailAlloc_916_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_38_(v___x_911_);
lean_dec_ref(v___x_911_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_snd_906_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_x_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
switch(lean_obj_tag(v_x_919_))
{
case 0:
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v___x_921_);
v_a_922_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_942_ == 0)
{
v___x_924_ = v_x_919_;
v_isShared_925_ = v_isSharedCheck_942_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_919_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_942_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v___x_926_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_927_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_926_, v_a_922_, v_a_920_);
v_fst_928_ = lean_ctor_get(v___x_927_, 0);
v_snd_929_ = lean_ctor_get(v___x_927_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_941_ == 0)
{
v___x_931_ = v___x_927_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_929_);
lean_inc(v_fst_928_);
lean_dec(v___x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_928_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_933_);
v___x_935_ = v___x_924_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_940_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_935_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_938_ = v___x_931_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_snd_929_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
case 1:
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_921_);
v_a_943_ = lean_ctor_get(v_x_919_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_961_ == 0)
{
v___x_945_ = v_x_919_;
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v_x_919_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v_fst_948_; lean_object* v_snd_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_960_; 
v___x_947_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_943_, v_a_920_);
v_fst_948_ = lean_ctor_get(v___x_947_, 0);
v_snd_949_ = lean_ctor_get(v___x_947_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_960_ == 0)
{
v___x_951_ = v___x_947_;
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_snd_949_);
lean_inc(v_fst_948_);
lean_dec(v___x_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_fst_948_);
v___x_954_ = v___x_945_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_948_);
v___x_954_ = v_reuseFailAlloc_959_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_954_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_snd_949_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
case 2:
{
lean_object* v_wi_962_; lean_object* v_alt_963_; lean_object* v___x_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_985_; 
v_wi_962_ = lean_ctor_get(v_x_919_, 0);
lean_inc_ref(v_wi_962_);
v_alt_963_ = lean_ctor_get(v_x_919_, 1);
lean_inc_ref(v_alt_963_);
lean_dec_ref_known(v_x_919_, 2);
v___x_964_ = l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_962_, v_a_920_);
v_fst_965_ = lean_ctor_get(v___x_964_, 0);
v_snd_966_ = lean_ctor_get(v___x_964_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_985_ == 0)
{
v___x_968_ = v___x_964_;
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v___x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v_fst_971_; lean_object* v_snd_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_984_; 
v___x_970_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_921_, v_alt_963_, v_snd_966_);
v_fst_971_ = lean_ctor_get(v___x_970_, 0);
v_snd_972_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_984_ == 0)
{
v___x_974_ = v___x_970_;
v_isShared_975_ = v_isSharedCheck_984_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_972_);
lean_inc(v_fst_971_);
lean_dec(v___x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_984_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_971_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 2);
lean_ctor_set(v___x_968_, 1, v___x_976_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_fst_965_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_983_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_978_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_979_);
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_snd_972_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
default: 
{
lean_object* v_indent_986_; lean_object* v_cls_987_; lean_object* v_msg_988_; uint8_t v_collapsed_989_; lean_object* v_children_990_; lean_object* v___x_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_994_; lean_object* v_fst_995_; lean_object* v_snd_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1012_; 
v_indent_986_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_indent_986_);
v_cls_987_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_cls_987_);
v_msg_988_ = lean_ctor_get(v_x_919_, 2);
lean_inc_ref(v_msg_988_);
v_collapsed_989_ = lean_ctor_get_uint8(v_x_919_, sizeof(void*)*4);
v_children_990_ = lean_ctor_get(v_x_919_, 3);
lean_inc_ref(v_children_990_);
lean_dec_ref_known(v_x_919_, 4);
v___x_991_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_921_, v_msg_988_, v_a_920_);
v_fst_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_fst_992_);
v_snd_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_snd_993_);
lean_dec_ref(v___x_991_);
v___x_994_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(v_children_990_, v_snd_993_);
v_fst_995_ = lean_ctor_get(v___x_994_, 0);
v_snd_996_ = lean_ctor_get(v___x_994_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_998_ = v___x_994_;
v_isShared_999_ = v_isSharedCheck_1012_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snd_996_);
lean_inc(v_fst_995_);
lean_dec(v___x_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1012_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1000_ = l_Lean_JsonNumber_fromNat(v_indent_986_);
v___x_1001_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
v___x_1002_ = 1;
v___x_1003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_cls_987_, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
v___x_1005_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_992_);
v___x_1006_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1006_, 0, v_collapsed_989_);
v___x_1007_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1004_);
lean_ctor_set(v___x_1007_, 2, v___x_1005_);
lean_ctor_set(v___x_1007_, 3, v___x_1006_);
lean_ctor_set(v___x_1007_, 4, v_fst_995_);
v___x_1008_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_65_(v___x_1007_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1008_);
v___x_1010_ = v___x_998_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_snd_996_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_bs_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_bs_1015_);
lean_ctor_set(v___x_1018_, 1, v___y_1016_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_v_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v_bs_x27_1025_; lean_object* v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1019_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
v_v_1020_ = lean_array_uget_borrowed(v_bs_1015_, v_i_1014_);
lean_inc(v_v_1020_);
v___x_1021_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_1019_, v_v_1020_, v___y_1016_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v___x_1021_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v_bs_x27_1025_ = lean_array_uset(v_bs_1015_, v_i_1014_, v___x_1024_);
v___x_1026_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_1022_);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1014_, v___x_1027_);
v___x_1029_ = lean_array_uset(v_bs_x27_1025_, v_i_1014_, v___x_1026_);
v_i_1014_ = v___x_1028_;
v_bs_1015_ = v___x_1029_;
v___y_1016_ = v_snd_1023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4___boxed(lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_bs_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_boxed_1035_, v_i_boxed_1036_, v_bs_1033_, v___y_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(lean_object* v_x_1038_){
_start:
{
lean_inc_ref(v_x_1038_);
return v_x_1038_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg___boxed(lean_object* v_x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(v_x_1039_);
lean_dec_ref(v_x_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(lean_object* v_00_u03b1_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_){
_start:
{
lean_inc_ref(v_x_1042_);
return v_x_1042_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(v_00_u03b1_1044_, v_x_1045_, v___y_1046_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_x_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object* v_json_1054_){
_start:
{
lean_object* v___x_1055_; 
lean_inc(v_json_1054_);
v___x_1055_ = l_Lean_Json_getTag_x3f(v_json_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_json_1054_);
v___x_1056_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0));
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1163_; 
v_val_1057_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1059_ = v___x_1055_;
v_isShared_1060_ = v_isSharedCheck_1163_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_val_1057_);
lean_dec(v___x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1163_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_1063_ = lean_string_dec_eq(v_val_1057_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
v___x_1065_ = lean_string_dec_eq(v_val_1057_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
lean_del_object(v___x_1059_);
v___x_1066_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_1067_ = lean_string_dec_eq(v_val_1057_, v___x_1066_);
lean_dec(v_val_1057_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_dec(v_json_1054_);
v___x_1068_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1));
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_unsigned_to_nat(2u);
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_Json_parseCtorFields(v_json_1054_, v___x_1066_, v___x_1069_, v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_a_1080_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_array_get_borrowed(v___x_1061_, v_a_1080_, v___x_1081_);
lean_inc(v___x_1082_);
v___x_1083_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec(v_a_1080_);
return v___x_1083_;
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_array_get(v___x_1061_, v_a_1080_, v___x_1088_);
lean_dec(v_a_1080_);
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1090_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_val_1057_);
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Lean_Json_parseCtorFields(v_json_1054_, v___x_1064_, v___x_1095_, v___x_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_del_object(v___x_1059_);
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_a_1106_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_array_get(v___x_1061_, v_a_1106_, v___x_1107_);
lean_dec(v_a_1106_);
v___x_1109_ = l_Lean_Json_getStr_x3f(v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_del_object(v___x_1059_);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_a_1118_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1120_ = v___x_1109_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1109_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1118_);
v___x_1123_ = v___x_1059_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_val_1057_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Lean_Json_parseCtorFields(v_json_1054_, v___x_1062_, v___x_1129_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_del_object(v___x_1059_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_a_1140_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_array_get(v___x_1061_, v_a_1140_, v___x_1141_);
lean_dec(v_a_1140_);
v___x_1143_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_1059_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v_a_1152_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1154_ = v___x_1143_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1143_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1152_);
v___x_1157_ = v___x_1059_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t v_sz_1164_, size_t v_i_1165_, lean_object* v_bs_1166_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1165_, v_sz_1164_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_bs_1166_);
return v___x_1168_;
}
else
{
lean_object* v_v_1169_; lean_object* v___x_1170_; 
v_v_1169_ = lean_array_uget_borrowed(v_bs_1166_, v_i_1165_);
lean_inc(v_v_1169_);
v___x_1170_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1169_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_bs_1166_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v_bs_x27_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v_a_1179_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1180_ = lean_unsigned_to_nat(0u);
v_bs_x27_1181_ = lean_array_uset(v_bs_1166_, v_i_1165_, v___x_1180_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1165_, v___x_1182_);
v___x_1184_ = lean_array_uset(v_bs_x27_1181_, v_i_1165_, v_a_1179_);
v_i_1165_ = v___x_1183_;
v_bs_1166_ = v___x_1184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 4)
{
lean_object* v_elems_1187_; size_t v_sz_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v_elems_1187_ = lean_ctor_get(v_x_1186_, 0);
lean_inc_ref(v_elems_1187_);
lean_dec_ref_known(v_x_1186_, 1);
v_sz_1188_ = lean_array_size(v_elems_1187_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_1188_, v___x_1189_, v_elems_1187_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1192_ = lean_unsigned_to_nat(80u);
v___x_1193_ = l_Lean_Json_pretty(v_x_1186_, v___x_1192_);
v___x_1194_ = lean_string_append(v___x_1191_, v___x_1193_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object* v_sz_1198_, lean_object* v_i_1199_, lean_object* v_bs_1200_){
_start:
{
size_t v_sz_boxed_1201_; size_t v_i_boxed_1202_; lean_object* v_res_1203_; 
v_sz_boxed_1201_ = lean_unbox_usize(v_sz_1198_);
lean_dec(v_sz_1198_);
v_i_boxed_1202_ = lean_unbox_usize(v_i_1199_);
lean_dec(v_i_1199_);
v_res_1203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_boxed_1201_, v_i_boxed_1202_, v_bs_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_bs_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_bs_1206_);
return v___x_1208_;
}
else
{
lean_object* v_v_1209_; lean_object* v___x_1210_; lean_object* v_bs_x27_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v_v_1209_ = lean_array_uget(v_bs_1206_, v_i_1205_);
v___x_1210_ = lean_unsigned_to_nat(0u);
v_bs_x27_1211_ = lean_array_uset(v_bs_1206_, v_i_1205_, v___x_1210_);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1205_, v___x_1212_);
v___x_1214_ = lean_array_uset(v_bs_x27_1211_, v_i_1205_, v_v_1209_);
v_i_1205_ = v___x_1213_;
v_bs_1206_ = v___x_1214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_bs_1218_){
_start:
{
size_t v_sz_boxed_1219_; size_t v_i_boxed_1220_; lean_object* v_res_1221_; 
v_sz_boxed_1219_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1220_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_boxed_1219_, v_i_boxed_1220_, v_bs_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 4)
{
lean_object* v_elems_1223_; size_t v_sz_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v_elems_1223_ = lean_ctor_get(v_x_1222_, 0);
lean_inc_ref(v_elems_1223_);
lean_dec_ref_known(v_x_1222_, 1);
v_sz_1224_ = lean_array_size(v_elems_1223_);
v___x_1225_ = ((size_t)0ULL);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_1224_, v___x_1225_, v_elems_1223_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1227_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1228_ = lean_unsigned_to_nat(80u);
v___x_1229_ = l_Lean_Json_pretty(v_x_1222_, v___x_1228_);
v___x_1230_ = lean_string_append(v___x_1227_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object* v_f_1234_, lean_object* v_x_1235_, lean_object* v___y_1236_){
_start:
{
switch(lean_obj_tag(v_x_1235_))
{
case 0:
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v_f_1234_);
v_a_1237_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v_x_1235_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v_x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
case 1:
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1272_; 
v_a_1246_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1248_ = v_x_1235_;
v_isShared_1249_ = v_isSharedCheck_1272_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v_x_1235_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1272_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
size_t v_sz_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v_sz_1250_ = lean_array_size(v_a_1246_);
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1234_, v_sz_1250_, v___x_1251_, v_a_1246_, v___y_1236_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_del_object(v___x_1248_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
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
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v_a_1261_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1263_ = v___x_1252_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1252_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_a_1261_);
v___x_1266_ = v___x_1248_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
default: 
{
lean_object* v_a_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1300_; 
v_a_1273_ = lean_ctor_get(v_x_1235_, 0);
v_a_1274_ = lean_ctor_get(v_x_1235_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1276_ = v_x_1235_;
v_isShared_1277_ = v_isSharedCheck_1300_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_inc(v_a_1273_);
lean_dec(v_x_1235_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1300_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
lean_inc_ref(v_f_1234_);
lean_inc_ref(v___y_1236_);
v___x_1278_ = lean_apply_2(v_f_1234_, v_a_1273_, v___y_1236_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1276_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_f_1234_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1288_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1234_, v_a_1274_, v___y_1236_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_dec(v_a_1287_);
lean_del_object(v___x_1276_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1299_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_a_1289_);
lean_ctor_set(v___x_1276_, 0, v_a_1287_);
v___x_1294_ = v___x_1276_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object* v_f_1301_, size_t v_sz_1302_, size_t v_i_1303_, lean_object* v_bs_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_lt(v_i_1303_, v_sz_1302_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref(v_f_1301_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_bs_1304_);
return v___x_1307_;
}
else
{
lean_object* v_v_1308_; lean_object* v___x_1309_; 
v_v_1308_ = lean_array_uget_borrowed(v_bs_1304_, v_i_1303_);
lean_inc(v_v_1308_);
lean_inc_ref(v_f_1301_);
v___x_1309_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1301_, v_v_1308_, v___y_1305_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_bs_1304_);
lean_dec_ref(v_f_1301_);
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v_bs_x27_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v_a_1318_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1319_ = lean_unsigned_to_nat(0u);
v_bs_x27_1320_ = lean_array_uset(v_bs_1304_, v_i_1303_, v___x_1319_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_add(v_i_1303_, v___x_1321_);
v___x_1323_ = lean_array_uset(v_bs_x27_1320_, v_i_1303_, v_a_1318_);
v_i_1303_ = v___x_1322_;
v_bs_1304_ = v___x_1323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object* v_f_1325_, lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_bs_1328_, lean_object* v___y_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1325_, v_sz_boxed_1330_, v_i_boxed_1331_, v_bs_1328_, v___y_1329_);
lean_dec_ref(v___y_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg___boxed(lean_object* v_f_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1333_, v_x_1334_, v___y_1335_);
lean_dec_ref(v___y_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object* v_j_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_1338_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; 
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1340_, 1);
if (lean_obj_tag(v_a_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1386_; 
v_a_1350_ = lean_ctor_get(v_a_1349_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_a_1349_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1352_ = v_a_1349_;
v_isShared_1353_ = v_isSharedCheck_1386_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_a_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1386_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(v_a_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_del_object(v___x_1352_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v_a_1363_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1354_, 1);
v_sz_1364_ = lean_array_size(v_a_1363_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_1364_, v___x_1365_, v_a_1363_, v_a_1339_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1352_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1385_; 
v_a_1375_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1377_ = v___x_1366_;
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1366_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_a_1375_);
v___x_1380_ = v___x_1352_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1412_; 
v_a_1387_ = lean_ctor_get(v_a_1349_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1349_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1389_ = v_a_1349_;
v_isShared_1390_ = v_isSharedCheck_1412_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v_a_1349_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1412_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_1392_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_1391_, v_a_1387_, v_a_1339_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_del_object(v___x_1389_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v_a_1401_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v___x_1392_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1392_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_a_1401_);
v___x_1406_ = v___x_1389_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_j_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(v_j_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1425_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
switch(lean_obj_tag(v_a_1424_))
{
case 0:
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v___x_1425_);
v_a_1426_ = lean_ctor_get(v_a_1424_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1428_ = v_a_1424_;
v_isShared_1429_ = v_isSharedCheck_1461_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v_a_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1461_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_a_1426_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_del_object(v___x_1428_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_a_1439_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1440_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_1441_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1440_, v_a_1439_, v_a_1414_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1428_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1460_; 
v_a_1450_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1452_ = v___x_1441_;
v_isShared_1453_ = v_isSharedCheck_1460_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1441_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1460_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v_a_1450_);
v___x_1455_ = v___x_1428_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
case 1:
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v___x_1425_);
v_a_1462_ = lean_ctor_get(v_a_1424_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1464_ = v_a_1424_;
v_isShared_1465_ = v_isSharedCheck_1486_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v_a_1424_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1486_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_1462_, v_a_1414_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_del_object(v___x_1464_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1485_; 
v_a_1475_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1477_ = v___x_1466_;
v_isShared_1478_ = v_isSharedCheck_1485_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1466_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1485_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_a_1475_);
v___x_1480_ = v___x_1464_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1480_);
v___x_1482_ = v___x_1477_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
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
case 2:
{
lean_object* v_wi_1487_; lean_object* v_alt_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1532_; 
v_wi_1487_ = lean_ctor_get(v_a_1424_, 0);
v_alt_1488_ = lean_ctor_get(v_a_1424_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1490_ = v_a_1424_;
v_isShared_1491_ = v_isSharedCheck_1532_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_alt_1488_);
lean_inc(v_wi_1487_);
lean_dec(v_a_1424_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1532_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_1487_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1490_);
lean_dec(v_alt_1488_);
lean_dec_ref(v___x_1425_);
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1502_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_alt_1488_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1501_);
lean_del_object(v___x_1490_);
lean_dec_ref(v___x_1425_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1512_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1425_, v_a_1511_, v_a_1414_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1501_);
lean_del_object(v___x_1490_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1531_; 
v_a_1521_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1523_ = v___x_1512_;
v_isShared_1524_ = v_isSharedCheck_1531_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1512_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1531_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_a_1521_);
lean_ctor_set(v___x_1490_, 0, v_a_1501_);
v___x_1526_ = v___x_1490_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1501_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
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
lean_object* v_indent_1533_; lean_object* v_cls_1534_; lean_object* v_msg_1535_; lean_object* v_collapsed_1536_; lean_object* v_children_1537_; lean_object* v___x_1538_; 
v_indent_1533_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_indent_1533_);
v_cls_1534_ = lean_ctor_get(v_a_1424_, 1);
lean_inc(v_cls_1534_);
v_msg_1535_ = lean_ctor_get(v_a_1424_, 2);
lean_inc(v_msg_1535_);
v_collapsed_1536_ = lean_ctor_get(v_a_1424_, 3);
lean_inc(v_collapsed_1536_);
v_children_1537_ = lean_ctor_get(v_a_1424_, 4);
lean_inc(v_children_1537_);
lean_dec_ref_known(v_a_1424_, 5);
v___x_1538_ = l_Lean_Json_getNat_x3f(v_indent_1533_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_children_1537_);
lean_dec(v_collapsed_1536_);
lean_dec(v_msg_1535_);
lean_dec(v_cls_1534_);
lean_dec_ref(v___x_1425_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1548_ = l_Lean_Name_fromJson_x3f(v_cls_1534_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_a_1547_);
lean_dec(v_children_1537_);
lean_dec(v_collapsed_1536_);
lean_dec(v_msg_1535_);
lean_dec_ref(v___x_1425_);
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1558_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_msg_1535_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1557_);
lean_dec(v_a_1547_);
lean_dec(v_children_1537_);
lean_dec(v_collapsed_1536_);
lean_dec_ref(v___x_1425_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1568_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1425_, v_a_1567_, v_a_1414_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1557_);
lean_dec(v_a_1547_);
lean_dec(v_children_1537_);
lean_dec(v_collapsed_1536_);
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1578_ = l_Lean_Json_getBool_x3f(v_collapsed_1536_);
lean_dec(v_collapsed_1536_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1577_);
lean_dec(v_a_1557_);
lean_dec(v_a_1547_);
lean_dec(v_children_1537_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1588_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_children_1537_, v_a_1414_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1577_);
lean_dec(v_a_1557_);
lean_dec(v_a_1547_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1606_; 
v_a_1597_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1599_ = v___x_1588_;
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1588_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_1601_, 0, v_a_1547_);
lean_ctor_set(v___x_1601_, 1, v_a_1557_);
lean_ctor_set(v___x_1601_, 2, v_a_1577_);
lean_ctor_set(v___x_1601_, 3, v_a_1597_);
v___x_1602_ = lean_unbox(v_a_1587_);
lean_dec(v_a_1587_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*4, v___x_1602_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1601_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed(lean_object* v_j_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(v_j_1607_, v_a_1608_);
lean_dec_ref(v_a_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t v_sz_1610_, size_t v_i_1611_, lean_object* v_bs_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_lt(v_i_1611_, v_sz_1610_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_bs_1612_);
return v___x_1615_;
}
else
{
lean_object* v_v_1616_; lean_object* v___x_1617_; 
v_v_1616_ = lean_array_uget_borrowed(v_bs_1612_, v_i_1611_);
lean_inc(v_v_1616_);
v___x_1617_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_bs_1612_);
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1627_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
v___x_1628_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1627_, v_a_1626_, v___y_1613_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_bs_1612_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v_bs_x27_1639_; size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v_a_1637_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1638_ = lean_unsigned_to_nat(0u);
v_bs_x27_1639_ = lean_array_uset(v_bs_1612_, v_i_1611_, v___x_1638_);
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_add(v_i_1611_, v___x_1640_);
v___x_1642_ = lean_array_uset(v_bs_x27_1639_, v_i_1611_, v_a_1637_);
v_i_1611_ = v___x_1641_;
v_bs_1612_ = v___x_1642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14___boxed(lean_object* v_sz_1644_, lean_object* v_i_1645_, lean_object* v_bs_1646_, lean_object* v___y_1647_){
_start:
{
size_t v_sz_boxed_1648_; size_t v_i_boxed_1649_; lean_object* v_res_1650_; 
v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1644_);
lean_dec(v_sz_1644_);
v_i_boxed_1649_ = lean_unbox_usize(v_i_1645_);
lean_dec(v_i_1645_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_boxed_1648_, v_i_boxed_1649_, v_bs_1646_, v___y_1647_);
lean_dec_ref(v___y_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7___boxed(lean_object* v_j_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_j_1651_, v_a_1652_);
lean_dec_ref(v_a_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_f_1656_, lean_object* v_x_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_1656_, v_x_1657_, v___y_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_f_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1662_, v_x_1663_, v___y_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_f_1668_, lean_object* v_x_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(v_00_u03b1_1666_, v_00_u03b2_1667_, v_f_1668_, v_x_1669_, v___y_1670_);
lean_dec_ref(v___y_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object* v_00_u03b1_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_f_1674_, size_t v_sz_1675_, size_t v_i_1676_, lean_object* v_bs_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_1674_, v_sz_1675_, v_i_1676_, v_bs_1677_, v___y_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_f_1682_, lean_object* v_sz_1683_, lean_object* v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_){
_start:
{
size_t v_sz_boxed_1687_; size_t v_i_boxed_1688_; lean_object* v_res_1689_; 
v_sz_boxed_1687_ = lean_unbox_usize(v_sz_1683_);
lean_dec(v_sz_1683_);
v_i_boxed_1688_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(v_00_u03b1_1680_, v_00_u03b2_1681_, v_f_1682_, v_sz_boxed_1687_, v_i_boxed_1688_, v_bs_1685_, v___y_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object* v_00_u03b1_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_f_1692_, size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_bs_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1692_, v_sz_1693_, v_i_1694_, v_bs_1695_, v___y_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_00_u03b2_1699_, lean_object* v_f_1700_, lean_object* v_sz_1701_, lean_object* v_i_1702_, lean_object* v_bs_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_sz_boxed_1705_; size_t v_i_boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1705_ = lean_unbox_usize(v_sz_1701_);
lean_dec(v_sz_1701_);
v_i_boxed_1706_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(v_00_u03b1_1698_, v_00_u03b2_1699_, v_f_1700_, v_sz_boxed_1705_, v_i_boxed_1706_, v_bs_1703_, v___y_1704_);
lean_dec_ref(v___y_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(lean_object* v_j_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = l_Lean_Json_getObjValD(v_j_1721_, v_k_1722_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0___boxed(lean_object* v_j_1725_, lean_object* v_k_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_j_1725_, v_k_1726_);
lean_dec_ref(v_k_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1730_) == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0));
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_x_1730_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(lean_object* v_j_1734_, lean_object* v_k_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = l_Lean_Json_getObjValD(v_j_1734_, v_k_1735_);
v___x_1737_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1___boxed(lean_object* v_j_1738_, lean_object* v_k_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_j_1738_, v_k_1739_);
lean_dec_ref(v_k_1739_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(lean_object* v_json_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_a_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
v___x_1753_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc_n(v_json_1752_, 10);
v___x_1754_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1752_, v___x_1753_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1757_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1756_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1760_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1759_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1763_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1762_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1766_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1765_);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1769_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1768_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1772_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1752_, v___x_1771_);
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1775_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1774_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1777_);
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1781_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1780_);
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1752_, v___x_1783_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1755_);
lean_ctor_set(v___x_1789_, 1, v_a_1758_);
lean_ctor_set(v___x_1789_, 2, v_a_1761_);
lean_ctor_set(v___x_1789_, 3, v_a_1764_);
lean_ctor_set(v___x_1789_, 4, v_a_1767_);
lean_ctor_set(v___x_1789_, 5, v_a_1770_);
lean_ctor_set(v___x_1789_, 6, v_a_1773_);
lean_ctor_set(v___x_1789_, 7, v_a_1776_);
lean_ctor_set(v___x_1789_, 8, v_a_1779_);
lean_ctor_set(v___x_1789_, 9, v_a_1782_);
lean_ctor_set(v___x_1789_, 10, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(lean_object* v_k_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1797_) == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v_k_1796_);
v___x_1798_ = lean_box(0);
return v___x_1798_;
}
else
{
lean_object* v_val_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_val_1799_ = lean_ctor_get(v_x_1797_, 0);
lean_inc(v_val_1799_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_k_1796_);
lean_ctor_set(v___x_1800_, 1, v_val_1799_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0___boxed(lean_object* v_k_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v_k_1803_, v_x_1804_);
lean_dec(v_x_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__1(lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
if (lean_obj_tag(v_a_1806_) == 0)
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_array_to_list(v_a_1807_);
return v___x_1808_;
}
else
{
lean_object* v_head_1809_; lean_object* v_tail_1810_; lean_object* v___x_1811_; 
v_head_1809_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_head_1809_);
v_tail_1810_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_tail_1810_);
lean_dec_ref_known(v_a_1806_, 2);
v___x_1811_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1807_, v_head_1809_);
v_a_1806_ = v_tail_1810_;
v_a_1807_ = v___x_1811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(lean_object* v_x_1815_){
_start:
{
lean_object* v_range_1816_; lean_object* v_fullRange_x3f_1817_; lean_object* v_severity_x3f_1818_; lean_object* v_isSilent_x3f_1819_; lean_object* v_code_x3f_1820_; lean_object* v_source_x3f_1821_; lean_object* v_message_1822_; lean_object* v_tags_x3f_1823_; lean_object* v_leanTags_x3f_1824_; lean_object* v_relatedInformation_x3f_1825_; lean_object* v_data_x3f_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_range_1816_ = lean_ctor_get(v_x_1815_, 0);
v_fullRange_x3f_1817_ = lean_ctor_get(v_x_1815_, 1);
v_severity_x3f_1818_ = lean_ctor_get(v_x_1815_, 2);
v_isSilent_x3f_1819_ = lean_ctor_get(v_x_1815_, 3);
v_code_x3f_1820_ = lean_ctor_get(v_x_1815_, 4);
v_source_x3f_1821_ = lean_ctor_get(v_x_1815_, 5);
v_message_1822_ = lean_ctor_get(v_x_1815_, 6);
v_tags_x3f_1823_ = lean_ctor_get(v_x_1815_, 7);
v_leanTags_x3f_1824_ = lean_ctor_get(v_x_1815_, 8);
v_relatedInformation_x3f_1825_ = lean_ctor_get(v_x_1815_, 9);
v_data_x3f_1826_ = lean_ctor_get(v_x_1815_, 10);
v___x_1827_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_range_1816_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v_range_1816_);
v___x_1829_ = lean_box(0);
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1832_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1831_, v_fullRange_x3f_1817_);
v___x_1833_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1834_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1833_, v_severity_x3f_1818_);
v___x_1835_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1836_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1835_, v_isSilent_x3f_1819_);
v___x_1837_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1838_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1837_, v_code_x3f_1820_);
v___x_1839_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1840_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1839_, v_source_x3f_1821_);
v___x_1841_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_message_1822_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_message_1822_);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1829_);
v___x_1844_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1845_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1844_, v_tags_x3f_1823_);
v___x_1846_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1847_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1846_, v_leanTags_x3f_1824_);
v___x_1848_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1849_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1848_, v_relatedInformation_x3f_1825_);
v___x_1850_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1851_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__0(v___x_1850_, v_data_x3f_1826_);
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1829_);
v___x_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1849_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1847_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1845_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1843_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1840_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1838_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1836_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1834_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1832_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1830_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_));
v___x_1864_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58__spec__1(v___x_1862_, v___x_1863_);
v___x_1865_ = l_Lean_Json_mkObj(v___x_1864_);
lean_dec(v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58____boxed(lean_object* v_x_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(v_x_1866_);
lean_dec_ref(v_x_1866_);
return v_res_1867_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = l_Lean_JsonNumber_fromNat(v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1873_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_unsigned_to_nat(2u);
v___x_1875_ = l_Lean_JsonNumber_fromNat(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1877_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1878_, lean_object* v___y_1879_){
_start:
{
if (v_a_1878_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___y_1879_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___y_1879_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1884_, lean_object* v___y_1885_){
_start:
{
uint8_t v_a_boxed_1886_; lean_object* v_res_1887_; 
v_a_boxed_1886_ = lean_unbox(v_a_1884_);
v_res_1887_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1886_, v___y_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_a_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_a_1888_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1892_, lean_object* v___y_1893_){
_start:
{
if (v_a_1892_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___y_1893_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___y_1893_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v_a_boxed_1900_; lean_object* v_res_1901_; 
v_a_boxed_1900_ = lean_unbox(v_a_1898_);
v_res_1901_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1900_, v___y_1899_);
return v_res_1901_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_unsigned_to_nat(3u);
v___x_1952_ = l_Lean_JsonNumber_fromNat(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1954_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_unsigned_to_nat(4u);
v___x_1956_ = l_Lean_JsonNumber_fromNat(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1958_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_range_1962_; lean_object* v_fullRange_x3f_1963_; lean_object* v_severity_x3f_1964_; lean_object* v_isSilent_x3f_1965_; lean_object* v_code_x3f_1966_; lean_object* v_source_x3f_1967_; lean_object* v_message_1968_; lean_object* v_tags_x3f_1969_; lean_object* v_leanTags_x3f_1970_; lean_object* v_relatedInformation_x3f_1971_; lean_object* v_data_x3f_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2167_; 
v_range_1962_ = lean_ctor_get(v_a_1960_, 0);
v_fullRange_x3f_1963_ = lean_ctor_get(v_a_1960_, 1);
v_severity_x3f_1964_ = lean_ctor_get(v_a_1960_, 2);
v_isSilent_x3f_1965_ = lean_ctor_get(v_a_1960_, 3);
v_code_x3f_1966_ = lean_ctor_get(v_a_1960_, 4);
v_source_x3f_1967_ = lean_ctor_get(v_a_1960_, 5);
v_message_1968_ = lean_ctor_get(v_a_1960_, 6);
v_tags_x3f_1969_ = lean_ctor_get(v_a_1960_, 7);
v_leanTags_x3f_1970_ = lean_ctor_get(v_a_1960_, 8);
v_relatedInformation_x3f_1971_ = lean_ctor_get(v_a_1960_, 9);
v_data_x3f_1972_ = lean_ctor_get(v_a_1960_, 10);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_1960_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_1974_ = v_a_1960_;
v_isShared_1975_ = v_isSharedCheck_2167_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_data_x3f_1972_);
lean_inc(v_relatedInformation_x3f_1971_);
lean_inc(v_leanTags_x3f_1970_);
lean_inc(v_tags_x3f_1969_);
lean_inc(v_message_1968_);
lean_inc(v_source_x3f_1967_);
lean_inc(v_code_x3f_1966_);
lean_inc(v_isSilent_x3f_1965_);
lean_inc(v_severity_x3f_1964_);
lean_inc(v_fullRange_x3f_1963_);
lean_inc(v_range_1962_);
lean_dec(v_a_1960_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2167_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___y_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___y_2143_; lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; 
v___f_1976_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1977_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1978_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_1979_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1962_);
if (lean_obj_tag(v_fullRange_x3f_1963_) == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_box(0);
v_fst_2148_ = v___x_2157_;
v_snd_2149_ = v_a_1961_;
goto v___jp_2147_;
}
else
{
lean_object* v_val_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
v_val_2158_ = lean_ctor_get(v_fullRange_x3f_1963_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_fullRange_x3f_1963_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v_fullRange_x3f_1963_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_val_2158_);
lean_dec(v_fullRange_x3f_1963_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_2158_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
v_fst_2148_ = v___x_2164_;
v_snd_2149_ = v_a_1961_;
goto v___jp_2147_;
}
}
}
v___jp_1980_:
{
lean_object* v___x_1992_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 9, v_fst_1989_);
lean_ctor_set(v___x_1974_, 8, v___y_1982_);
lean_ctor_set(v___x_1974_, 7, v___y_1988_);
lean_ctor_set(v___x_1974_, 6, v___y_1984_);
lean_ctor_set(v___x_1974_, 5, v___y_1981_);
lean_ctor_set(v___x_1974_, 4, v___y_1985_);
lean_ctor_set(v___x_1974_, 3, v___y_1987_);
lean_ctor_set(v___x_1974_, 2, v___y_1983_);
lean_ctor_set(v___x_1974_, 1, v___y_1986_);
lean_ctor_set(v___x_1974_, 0, v___x_1979_);
v___x_1992_ = v___x_1974_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___y_1986_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v___y_1983_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v___y_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v___y_1985_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v___y_1981_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v___y_1984_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v___y_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v___y_1982_);
lean_ctor_set(v_reuseFailAlloc_1995_, 9, v_fst_1989_);
lean_ctor_set(v_reuseFailAlloc_1995_, 10, v_data_x3f_1972_);
v___x_1992_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_58_(v___x_1992_);
lean_dec_ref(v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v_snd_1990_);
return v___x_1994_;
}
}
v___jp_1996_:
{
lean_object* v___x_2006_; 
v___x_2006_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_relatedInformation_x3f_1971_) == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_box(0);
v___y_1981_ = v___y_1997_;
v___y_1982_ = v_fst_2004_;
v___y_1983_ = v___y_1998_;
v___y_1984_ = v___y_2000_;
v___y_1985_ = v___y_1999_;
v___y_1986_ = v___y_2001_;
v___y_1987_ = v___y_2002_;
v___y_1988_ = v___y_2003_;
v_fst_1989_ = v___x_2007_;
v_snd_1990_ = v_snd_2005_;
goto v___jp_1980_;
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2023_; 
v_val_2008_ = lean_ctor_get(v_relatedInformation_x3f_1971_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_relatedInformation_x3f_1971_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2010_ = v_relatedInformation_x3f_1971_;
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_relatedInformation_x3f_1971_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
size_t v_sz_2012_; size_t v___x_2013_; lean_object* v___x_7261__overap_2014_; lean_object* v___x_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v_sz_2012_ = lean_array_size(v_val_2008_);
v___x_2013_ = ((size_t)0ULL);
v___x_7261__overap_2014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2006_, v___f_1977_, v_sz_2012_, v___x_2013_, v_val_2008_);
v___x_2015_ = lean_apply_1(v___x_7261__overap_2014_, v_snd_2005_);
v_fst_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_fst_2016_);
v_snd_2017_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_snd_2017_);
lean_dec_ref(v___x_2015_);
v___x_2018_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2019_ = l_Lean_Array_toJson___redArg(v___x_2018_, v_fst_2016_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2019_);
v___x_2021_ = v___x_2010_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
v___y_1981_ = v___y_1997_;
v___y_1982_ = v_fst_2004_;
v___y_1983_ = v___y_1998_;
v___y_1984_ = v___y_2000_;
v___y_1985_ = v___y_1999_;
v___y_1986_ = v___y_2001_;
v___y_1987_ = v___y_2002_;
v___y_1988_ = v___y_2003_;
v_fst_1989_ = v___x_2021_;
v_snd_1990_ = v_snd_2017_;
goto v___jp_1980_;
}
}
}
}
v___jp_2024_:
{
lean_object* v___x_2033_; 
v___x_2033_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_leanTags_x3f_1970_) == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_box(0);
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2027_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v_fst_2031_;
v_fst_2004_ = v___x_2034_;
v_snd_2005_ = v_snd_2032_;
goto v___jp_1996_;
}
else
{
lean_object* v_val_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2050_; 
v_val_2035_ = lean_ctor_get(v_leanTags_x3f_1970_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_leanTags_x3f_1970_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2037_ = v_leanTags_x3f_1970_;
v_isShared_2038_ = v_isSharedCheck_2050_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_val_2035_);
lean_dec(v_leanTags_x3f_1970_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2050_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
size_t v_sz_2039_; size_t v___x_2040_; lean_object* v___x_7285__overap_2041_; lean_object* v___x_2042_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v_sz_2039_ = lean_array_size(v_val_2035_);
v___x_2040_ = ((size_t)0ULL);
v___x_7285__overap_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2033_, v___f_1976_, v_sz_2039_, v___x_2040_, v_val_2035_);
v___x_2042_ = lean_apply_1(v___x_7285__overap_2041_, v_snd_2032_);
v_fst_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_fst_2043_);
v_snd_2044_ = lean_ctor_get(v___x_2042_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2042_);
v___x_2045_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2046_ = l_Lean_Array_toJson___redArg(v___x_2045_, v_fst_2043_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2046_);
v___x_2048_ = v___x_2037_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2026_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2027_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v_fst_2031_;
v_fst_2004_ = v___x_2048_;
v_snd_2005_ = v_snd_2044_;
goto v___jp_1996_;
}
}
}
}
v___jp_2051_:
{
lean_object* v_rpcEncode_2058_; lean_object* v___x_2059_; lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v___x_2062_; 
v_rpcEncode_2058_ = lean_ctor_get(v_inst_1959_, 0);
lean_inc_ref(v_rpcEncode_2058_);
lean_dec_ref(v_inst_1959_);
v___x_2059_ = lean_apply_2(v_rpcEncode_2058_, v_message_1968_, v_snd_2057_);
v_fst_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_fst_2060_);
v_snd_2061_ = lean_ctor_get(v___x_2059_, 1);
lean_inc(v_snd_2061_);
lean_dec_ref(v___x_2059_);
v___x_2062_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_tags_x3f_1969_) == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_box(0);
v___y_2025_ = v_fst_2056_;
v___y_2026_ = v___y_2052_;
v___y_2027_ = v_fst_2060_;
v___y_2028_ = v___y_2053_;
v___y_2029_ = v___y_2054_;
v___y_2030_ = v___y_2055_;
v_fst_2031_ = v___x_2063_;
v_snd_2032_ = v_snd_2061_;
goto v___jp_2024_;
}
else
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2079_; 
v_val_2064_ = lean_ctor_get(v_tags_x3f_1969_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_tags_x3f_1969_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2066_ = v_tags_x3f_1969_;
v_isShared_2067_ = v_isSharedCheck_2079_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v_tags_x3f_1969_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2079_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_7309__overap_2070_; lean_object* v___x_2071_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v_sz_2068_ = lean_array_size(v_val_2064_);
v___x_2069_ = ((size_t)0ULL);
v___x_7309__overap_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2062_, v___f_1978_, v_sz_2068_, v___x_2069_, v_val_2064_);
v___x_2071_ = lean_apply_1(v___x_7309__overap_2070_, v_snd_2061_);
v_fst_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_fst_2072_);
v_snd_2073_ = lean_ctor_get(v___x_2071_, 1);
lean_inc(v_snd_2073_);
lean_dec_ref(v___x_2071_);
v___x_2074_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2075_ = l_Lean_Array_toJson___redArg(v___x_2074_, v_fst_2072_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2075_);
v___x_2077_ = v___x_2066_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v___y_2025_ = v_fst_2056_;
v___y_2026_ = v___y_2052_;
v___y_2027_ = v_fst_2060_;
v___y_2028_ = v___y_2053_;
v___y_2029_ = v___y_2054_;
v___y_2030_ = v___y_2055_;
v_fst_2031_ = v___x_2077_;
v_snd_2032_ = v_snd_2073_;
goto v___jp_2024_;
}
}
}
}
v___jp_2080_:
{
if (lean_obj_tag(v_source_x3f_1967_) == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_box(0);
v___y_2052_ = v___y_2081_;
v___y_2053_ = v_fst_2084_;
v___y_2054_ = v___y_2082_;
v___y_2055_ = v___y_2083_;
v_fst_2056_ = v___x_2086_;
v_snd_2057_ = v_snd_2085_;
goto v___jp_2051_;
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
v_val_2087_ = lean_ctor_get(v_source_x3f_1967_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_source_x3f_1967_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2089_ = v_source_x3f_1967_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v_source_x3f_1967_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_val_2087_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v___y_2052_ = v___y_2081_;
v___y_2053_ = v_fst_2084_;
v___y_2054_ = v___y_2082_;
v___y_2055_ = v___y_2083_;
v_fst_2056_ = v___x_2093_;
v_snd_2057_ = v_snd_2085_;
goto v___jp_2051_;
}
}
}
}
v___jp_2096_:
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_fst_2100_);
v___y_2081_ = v___y_2097_;
v___y_2082_ = v___y_2098_;
v___y_2083_ = v___y_2099_;
v_fst_2084_ = v___x_2102_;
v_snd_2085_ = v_snd_2101_;
goto v___jp_2080_;
}
v___jp_2103_:
{
if (lean_obj_tag(v_code_x3f_1966_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_box(0);
v___y_2081_ = v___y_2104_;
v___y_2082_ = v___y_2105_;
v___y_2083_ = v_fst_2106_;
v_fst_2084_ = v___x_2108_;
v_snd_2085_ = v_snd_2107_;
goto v___jp_2080_;
}
else
{
lean_object* v_val_2109_; 
v_val_2109_ = lean_ctor_get(v_code_x3f_1966_, 0);
lean_inc(v_val_2109_);
lean_dec_ref_known(v_code_x3f_1966_, 1);
if (lean_obj_tag(v_val_2109_) == 0)
{
lean_object* v_i_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_i_2110_ = lean_ctor_get(v_val_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_val_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v_val_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_i_2110_);
lean_dec(v_val_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = l_Lean_JsonNumber_fromInt(v_i_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 2);
lean_ctor_set(v___x_2112_, 0, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
v___y_2097_ = v___y_2104_;
v___y_2098_ = v___y_2105_;
v___y_2099_ = v_fst_2106_;
v_fst_2100_ = v___x_2116_;
v_snd_2101_ = v_snd_2107_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v_s_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_s_2119_ = lean_ctor_get(v_val_2109_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_val_2109_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v_val_2109_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_s_2119_);
lean_dec(v_val_2109_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 3);
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_s_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v___y_2097_ = v___y_2104_;
v___y_2098_ = v___y_2105_;
v___y_2099_ = v_fst_2106_;
v_fst_2100_ = v___x_2124_;
v_snd_2101_ = v_snd_2107_;
goto v___jp_2096_;
}
}
}
}
}
v___jp_2127_:
{
if (lean_obj_tag(v_isSilent_x3f_1965_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_box(0);
v___y_2104_ = v_fst_2129_;
v___y_2105_ = v___y_2128_;
v_fst_2106_ = v___x_2131_;
v_snd_2107_ = v_snd_2130_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2141_; 
v_val_2132_ = lean_ctor_get(v_isSilent_x3f_1965_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_isSilent_x3f_1965_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2134_ = v_isSilent_x3f_1965_;
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_val_2132_);
lean_dec(v_isSilent_x3f_1965_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2139_; 
v___x_2136_ = lean_alloc_ctor(1, 0, 1);
v___x_2137_ = lean_unbox(v_val_2132_);
lean_dec(v_val_2132_);
lean_ctor_set_uint8(v___x_2136_, 0, v___x_2137_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2139_ = v___x_2134_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2136_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_2104_ = v_fst_2129_;
v___y_2105_ = v___y_2128_;
v_fst_2106_ = v___x_2139_;
v_snd_2107_ = v_snd_2130_;
goto v___jp_2103_;
}
}
}
}
v___jp_2142_:
{
lean_object* v___x_2146_; 
lean_inc(v_fst_2144_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_fst_2144_);
v___y_2128_ = v___y_2143_;
v_fst_2129_ = v___x_2146_;
v_snd_2130_ = v_snd_2145_;
goto v___jp_2127_;
}
v___jp_2147_:
{
if (lean_obj_tag(v_severity_x3f_1964_) == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_box(0);
v___y_2128_ = v_fst_2148_;
v_fst_2129_ = v___x_2150_;
v_snd_2130_ = v_snd_2149_;
goto v___jp_2127_;
}
else
{
lean_object* v_val_2151_; uint8_t v___x_2152_; 
v_val_2151_ = lean_ctor_get(v_severity_x3f_1964_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v_severity_x3f_1964_, 1);
v___x_2152_ = lean_unbox(v_val_2151_);
lean_dec(v_val_2151_);
switch(v___x_2152_)
{
case 0:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2143_ = v_fst_2148_;
v_fst_2144_ = v___x_2153_;
v_snd_2145_ = v_snd_2149_;
goto v___jp_2142_;
}
case 1:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2143_ = v_fst_2148_;
v_fst_2144_ = v___x_2154_;
v_snd_2145_ = v_snd_2149_;
goto v___jp_2142_;
}
case 2:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2143_ = v_fst_2148_;
v_fst_2144_ = v___x_2155_;
v_snd_2145_ = v_snd_2149_;
goto v___jp_2142_;
}
default: 
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2143_ = v_fst_2148_;
v_fst_2144_ = v___x_2156_;
v_snd_2145_ = v_snd_2149_;
goto v___jp_2142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2168_, lean_object* v_inst_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2169_, v_a_2170_, v_a_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v_j_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_10463__overap_2178_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_j_2175_);
v___x_10463__overap_2178_ = l_MonadExcept_ofExcept___redArg(v___x_2173_, v___x_2174_, v___x_2177_);
lean_inc_ref(v___y_2176_);
v___x_2179_ = lean_apply_1(v___x_10463__overap_2178_, v___y_2176_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v_j_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2180_, v___x_2181_, v_j_2182_, v___y_2183_);
lean_dec_ref(v___y_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2194_, lean_object* v___x_2195_, lean_object* v_j_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_Json_getNat_x3f(v_j_2196_);
if (lean_obj_tag(v___x_2202_) == 1)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_dec_eq(v_a_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_unsigned_to_nat(2u);
v___x_2207_ = lean_nat_dec_eq(v_a_2203_, v___x_2206_);
lean_dec(v_a_2203_);
if (v___x_2207_ == 0)
{
goto v___jp_2198_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_10479__overap_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10479__overap_2209_ = l_MonadExcept_ofExcept___redArg(v___x_2194_, v___x_2195_, v___x_2208_);
lean_inc_ref(v___y_2197_);
v___x_2210_ = lean_apply_1(v___x_10479__overap_2209_, v___y_2197_);
return v___x_2210_;
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_10482__overap_2212_; lean_object* v___x_2213_; 
lean_dec(v_a_2203_);
v___x_2211_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10482__overap_2212_ = l_MonadExcept_ofExcept___redArg(v___x_2194_, v___x_2195_, v___x_2211_);
lean_inc_ref(v___y_2197_);
v___x_2213_ = lean_apply_1(v___x_10482__overap_2212_, v___y_2197_);
return v___x_2213_;
}
}
else
{
lean_dec_ref(v___x_2202_);
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v___x_2199_; lean_object* v___x_10470__overap_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10470__overap_2200_ = l_MonadExcept_ofExcept___redArg(v___x_2194_, v___x_2195_, v___x_2199_);
lean_inc_ref(v___y_2197_);
v___x_2201_ = lean_apply_1(v___x_10470__overap_2200_, v___y_2197_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2214_, lean_object* v___x_2215_, lean_object* v_j_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2214_, v___x_2215_, v_j_2216_, v___y_2217_);
lean_dec_ref(v___y_2217_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2228_, lean_object* v___x_2229_, lean_object* v_j_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Json_getNat_x3f(v_j_2230_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_dec_eq(v_a_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_unsigned_to_nat(2u);
v___x_2241_ = lean_nat_dec_eq(v_a_2237_, v___x_2240_);
lean_dec(v_a_2237_);
if (v___x_2241_ == 0)
{
goto v___jp_2232_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_10498__overap_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10498__overap_2243_ = l_MonadExcept_ofExcept___redArg(v___x_2228_, v___x_2229_, v___x_2242_);
lean_inc_ref(v___y_2231_);
v___x_2244_ = lean_apply_1(v___x_10498__overap_2243_, v___y_2231_);
return v___x_2244_;
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_10501__overap_2246_; lean_object* v___x_2247_; 
lean_dec(v_a_2237_);
v___x_2245_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10501__overap_2246_ = l_MonadExcept_ofExcept___redArg(v___x_2228_, v___x_2229_, v___x_2245_);
lean_inc_ref(v___y_2231_);
v___x_2247_ = lean_apply_1(v___x_10501__overap_2246_, v___y_2231_);
return v___x_2247_;
}
}
else
{
lean_dec_ref(v___x_2236_);
goto v___jp_2232_;
}
v___jp_2232_:
{
lean_object* v___x_2233_; lean_object* v___x_10489__overap_2234_; lean_object* v___x_2235_; 
v___x_2233_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10489__overap_2234_ = l_MonadExcept_ofExcept___redArg(v___x_2228_, v___x_2229_, v___x_2233_);
lean_inc_ref(v___y_2231_);
v___x_2235_ = lean_apply_1(v___x_10489__overap_2234_, v___y_2231_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2248_, lean_object* v___x_2249_, lean_object* v_j_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2248_, v___x_2249_, v_j_2250_, v___y_2251_);
lean_dec_ref(v___y_2251_);
return v_res_2252_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2254_ = l_ReaderT_instMonad___redArg(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___f_2256_; 
v___x_2255_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2256_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2256_, 0, v___x_2255_);
return v___f_2256_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___f_2258_; 
v___x_2257_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2258_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_2258_, 0, v___x_2257_);
return v___f_2258_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___f_2260_; 
v___x_2259_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2260_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_2260_, 0, v___x_2259_);
return v___f_2260_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___f_2262_; 
v___x_2261_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2262_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_2262_, 0, v___x_2261_);
return v___f_2262_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2264_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_2264_, 0, lean_box(0));
lean_closure_set(v___x_2264_, 1, lean_box(0));
lean_closure_set(v___x_2264_, 2, v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___f_2265_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2266_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___f_2265_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2269_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_2269_, 0, lean_box(0));
lean_closure_set(v___x_2269_, 1, lean_box(0));
lean_closure_set(v___x_2269_, 2, v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___f_2270_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2271_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2272_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2273_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2274_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2273_);
lean_ctor_set(v___x_2275_, 2, v___f_2272_);
lean_ctor_set(v___x_2275_, 3, v___f_2271_);
lean_ctor_set(v___x_2275_, 4, v___f_2270_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2277_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_2277_, 0, lean_box(0));
lean_closure_set(v___x_2277_, 1, lean_box(0));
lean_closure_set(v___x_2277_, 2, v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2279_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2278_);
return v___x_2280_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2282_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_2282_, 0, lean_box(0));
lean_closure_set(v___x_2282_, 1, lean_box(0));
lean_closure_set(v___x_2282_, 2, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_2298_, lean_object* v_j_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(v_j_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_inst_2298_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2743_; 
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2312_ = v___x_2301_;
v_isShared_2313_ = v_isSharedCheck_2743_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2743_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_toApplicative_2316_; lean_object* v_toPure_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_range_2322_; lean_object* v_fullRange_x3f_2323_; lean_object* v_severity_x3f_2324_; lean_object* v_isSilent_x3f_2325_; lean_object* v_code_x3f_2326_; lean_object* v_source_x3f_2327_; lean_object* v_message_2328_; lean_object* v_tags_x3f_2329_; lean_object* v_leanTags_x3f_2330_; lean_object* v_relatedInformation_x3f_2331_; lean_object* v_data_x3f_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2742_; 
v___x_2314_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2315_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v_toApplicative_2316_ = lean_ctor_get(v___x_2314_, 0);
v_toPure_2317_ = lean_ctor_get(v_toApplicative_2316_, 1);
lean_inc(v_toPure_2317_);
v___f_2318_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2318_, 0, v_toPure_2317_);
v___x_2319_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___f_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2320_);
v_range_2322_ = lean_ctor_get(v_a_2310_, 0);
v_fullRange_x3f_2323_ = lean_ctor_get(v_a_2310_, 1);
v_severity_x3f_2324_ = lean_ctor_get(v_a_2310_, 2);
v_isSilent_x3f_2325_ = lean_ctor_get(v_a_2310_, 3);
v_code_x3f_2326_ = lean_ctor_get(v_a_2310_, 4);
v_source_x3f_2327_ = lean_ctor_get(v_a_2310_, 5);
v_message_2328_ = lean_ctor_get(v_a_2310_, 6);
v_tags_x3f_2329_ = lean_ctor_get(v_a_2310_, 7);
v_leanTags_x3f_2330_ = lean_ctor_get(v_a_2310_, 8);
v_relatedInformation_x3f_2331_ = lean_ctor_get(v_a_2310_, 9);
v_data_x3f_2332_ = lean_ctor_get(v_a_2310_, 10);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2310_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2334_ = v_a_2310_;
v_isShared_2335_ = v_isSharedCheck_2742_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_data_x3f_2332_);
lean_inc(v_relatedInformation_x3f_2331_);
lean_inc(v_leanTags_x3f_2330_);
lean_inc(v_tags_x3f_2329_);
lean_inc(v_message_2328_);
lean_inc(v_source_x3f_2327_);
lean_inc(v_code_x3f_2326_);
lean_inc(v_isSilent_x3f_2325_);
lean_inc(v_severity_x3f_2324_);
lean_inc(v_fullRange_x3f_2323_);
lean_inc(v_range_2322_);
lean_dec(v_a_2310_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2742_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_10349__overap_2337_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_range_2322_);
lean_inc_ref(v___x_2321_);
v___x_10349__overap_2337_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2336_);
lean_inc_ref(v_a_2300_);
v___x_2338_ = lean_apply_1(v___x_10349__overap_2337_, v_a_2300_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec(v_source_x3f_2327_);
lean_dec(v_code_x3f_2326_);
lean_dec(v_isSilent_x3f_2325_);
lean_dec(v_severity_x3f_2324_);
lean_dec(v_fullRange_x3f_2323_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2741_; 
v_a_2347_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2349_ = v___x_2338_;
v_isShared_2350_ = v_isSharedCheck_2741_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2338_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2741_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v_____do__lift_2361_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v_____do__lift_2377_; lean_object* v___y_2378_; lean_object* v___f_2401_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v_____do__lift_2410_; lean_object* v___y_2411_; lean_object* v___f_2445_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v_____do__lift_2453_; lean_object* v___y_2454_; lean_object* v___f_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v_____do__lift_2494_; lean_object* v___y_2495_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v_____do__lift_2545_; lean_object* v___y_2546_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v_j_2589_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v_____do__lift_2602_; lean_object* v___y_2603_; lean_object* v___y_2642_; lean_object* v_____do__lift_2643_; lean_object* v___y_2644_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v_____do__lift_2694_; lean_object* v___y_2695_; 
lean_inc_ref_n(v___x_2321_, 3);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2401_, 0, v___x_2315_);
lean_closure_set(v___f_2401_, 1, v___x_2321_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2445_, 0, v___x_2315_);
lean_closure_set(v___f_2445_, 1, v___x_2321_);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2488_, 0, v___x_2315_);
lean_closure_set(v___f_2488_, 1, v___x_2321_);
if (lean_obj_tag(v_fullRange_x3f_2323_) == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_box(0);
v_____do__lift_2694_ = v___x_2720_;
v___y_2695_ = v_a_2300_;
goto v___jp_2693_;
}
else
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2740_; 
v_val_2721_ = lean_ctor_get(v_fullRange_x3f_2323_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_fullRange_x3f_2323_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2723_ = v_fullRange_x3f_2323_;
v_isShared_2724_ = v_isSharedCheck_2740_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v_fullRange_x3f_2323_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2740_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_10402__overap_2726_; lean_object* v___x_2727_; 
v___x_2725_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_2721_);
lean_inc_ref(v___x_2321_);
v___x_10402__overap_2726_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2725_);
lean_inc_ref(v_a_2300_);
v___x_2727_ = lean_apply_1(v___x_10402__overap_2726_, v_a_2300_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_del_object(v___x_2723_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec(v_source_x3f_2327_);
lean_dec(v_code_x3f_2326_);
lean_dec(v_isSilent_x3f_2325_);
lean_dec(v_severity_x3f_2324_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2727_, 1);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v_a_2736_);
v___x_2738_ = v___x_2723_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
v_____do__lift_2694_ = v___x_2738_;
v___y_2695_ = v_a_2300_;
goto v___jp_2693_;
}
}
}
}
v___jp_2351_:
{
lean_object* v___x_2363_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 10, v_____do__lift_2361_);
lean_ctor_set(v___x_2334_, 9, v___y_2355_);
lean_ctor_set(v___x_2334_, 8, v___y_2356_);
lean_ctor_set(v___x_2334_, 7, v___y_2360_);
lean_ctor_set(v___x_2334_, 6, v___y_2357_);
lean_ctor_set(v___x_2334_, 5, v___y_2359_);
lean_ctor_set(v___x_2334_, 4, v___y_2353_);
lean_ctor_set(v___x_2334_, 3, v___y_2358_);
lean_ctor_set(v___x_2334_, 2, v___y_2354_);
lean_ctor_set(v___x_2334_, 1, v___y_2352_);
lean_ctor_set(v___x_2334_, 0, v_a_2347_);
v___x_2363_ = v___x_2334_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2347_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v___y_2352_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v___y_2354_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v___y_2358_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v___y_2353_);
lean_ctor_set(v_reuseFailAlloc_2367_, 5, v___y_2359_);
lean_ctor_set(v_reuseFailAlloc_2367_, 6, v___y_2357_);
lean_ctor_set(v_reuseFailAlloc_2367_, 7, v___y_2360_);
lean_ctor_set(v_reuseFailAlloc_2367_, 8, v___y_2356_);
lean_ctor_set(v_reuseFailAlloc_2367_, 9, v___y_2355_);
lean_ctor_set(v_reuseFailAlloc_2367_, 10, v_____do__lift_2361_);
v___x_2363_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2363_);
v___x_2365_ = v___x_2349_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
v___jp_2368_:
{
if (lean_obj_tag(v_data_x3f_2332_) == 0)
{
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v___y_2352_ = v___y_2369_;
v___y_2353_ = v___y_2371_;
v___y_2354_ = v___y_2370_;
v___y_2355_ = v_____do__lift_2377_;
v___y_2356_ = v___y_2372_;
v___y_2357_ = v___y_2373_;
v___y_2358_ = v___y_2374_;
v___y_2359_ = v___y_2375_;
v___y_2360_ = v___y_2376_;
v_____do__lift_2361_ = v_data_x3f_2332_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2400_; 
v_val_2379_ = lean_ctor_get(v_data_x3f_2332_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_data_x3f_2332_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2381_ = v_data_x3f_2332_;
v_isShared_2382_ = v_isSharedCheck_2400_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v_data_x3f_2332_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2400_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_val_2379_);
v___x_2384_ = v___x_2312_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_val_2379_);
v___x_2384_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_10351__overap_2385_; lean_object* v___x_2386_; 
v___x_10351__overap_2385_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2384_);
lean_inc_ref(v___y_2378_);
v___x_2386_ = lean_apply_1(v___x_10351__overap_2385_, v___y_2378_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_del_object(v___x_2381_);
lean_dec(v_____do__lift_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec(v___y_2369_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2386_, 1);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_a_2395_);
v___x_2397_ = v___x_2381_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v___y_2352_ = v___y_2369_;
v___y_2353_ = v___y_2371_;
v___y_2354_ = v___y_2370_;
v___y_2355_ = v_____do__lift_2377_;
v___y_2356_ = v___y_2372_;
v___y_2357_ = v___y_2373_;
v___y_2358_ = v___y_2374_;
v___y_2359_ = v___y_2375_;
v___y_2360_ = v___y_2376_;
v_____do__lift_2361_ = v___x_2397_;
goto v___jp_2351_;
}
}
}
}
}
}
v___jp_2402_:
{
if (lean_obj_tag(v_relatedInformation_x3f_2331_) == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___f_2401_);
v___x_2412_ = lean_box(0);
v___y_2369_ = v___y_2403_;
v___y_2370_ = v___y_2405_;
v___y_2371_ = v___y_2404_;
v___y_2372_ = v_____do__lift_2410_;
v___y_2373_ = v___y_2406_;
v___y_2374_ = v___y_2407_;
v___y_2375_ = v___y_2408_;
v___y_2376_ = v___y_2409_;
v_____do__lift_2377_ = v___x_2412_;
v___y_2378_ = v___y_2411_;
goto v___jp_2368_;
}
else
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2444_; 
v_val_2413_ = lean_ctor_get(v_relatedInformation_x3f_2331_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_relatedInformation_x3f_2331_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2415_ = v_relatedInformation_x3f_2331_;
v_isShared_2416_ = v_isSharedCheck_2444_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v_relatedInformation_x3f_2331_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2444_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___f_2417_; lean_object* v___x_2418_; 
v___f_2417_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2418_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2417_, v_val_2413_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_del_object(v___x_2415_);
lean_dec(v_____do__lift_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_object* v_a_2427_; size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_10103__overap_2430_; lean_object* v___x_2431_; 
v_a_2427_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2418_, 1);
v_sz_2428_ = lean_array_size(v_a_2427_);
v___x_2429_ = ((size_t)0ULL);
v___x_10103__overap_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2315_, v___f_2401_, v_sz_2428_, v___x_2429_, v_a_2427_);
lean_inc_ref(v___y_2411_);
v___x_2431_ = lean_apply_1(v___x_10103__overap_2430_, v___y_2411_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_del_object(v___x_2415_);
lean_dec(v_____do__lift_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2403_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2431_, 1);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v_a_2440_);
v___x_2442_ = v___x_2415_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
v___y_2369_ = v___y_2403_;
v___y_2370_ = v___y_2405_;
v___y_2371_ = v___y_2404_;
v___y_2372_ = v_____do__lift_2410_;
v___y_2373_ = v___y_2406_;
v___y_2374_ = v___y_2407_;
v___y_2375_ = v___y_2408_;
v___y_2376_ = v___y_2409_;
v_____do__lift_2377_ = v___x_2442_;
v___y_2378_ = v___y_2411_;
goto v___jp_2368_;
}
}
}
}
}
}
v___jp_2446_:
{
if (lean_obj_tag(v_leanTags_x3f_2330_) == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v___f_2445_);
v___x_2455_ = lean_box(0);
v___y_2403_ = v___y_2447_;
v___y_2404_ = v___y_2449_;
v___y_2405_ = v___y_2448_;
v___y_2406_ = v___y_2450_;
v___y_2407_ = v___y_2451_;
v___y_2408_ = v___y_2452_;
v___y_2409_ = v_____do__lift_2453_;
v_____do__lift_2410_ = v___x_2455_;
v___y_2411_ = v___y_2454_;
goto v___jp_2402_;
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2487_; 
v_val_2456_ = lean_ctor_get(v_leanTags_x3f_2330_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_leanTags_x3f_2330_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2458_ = v_leanTags_x3f_2330_;
v_isShared_2459_ = v_isSharedCheck_2487_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_val_2456_);
lean_dec(v_leanTags_x3f_2330_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2487_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___f_2460_; lean_object* v___x_2461_; 
v___f_2460_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2461_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2460_, v_val_2456_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_del_object(v___x_2458_);
lean_dec(v_____do__lift_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_object* v_a_2470_; size_t v_sz_2471_; size_t v___x_2472_; lean_object* v___x_10154__overap_2473_; lean_object* v___x_2474_; 
v_a_2470_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2461_, 1);
v_sz_2471_ = lean_array_size(v_a_2470_);
v___x_2472_ = ((size_t)0ULL);
v___x_10154__overap_2473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2315_, v___f_2445_, v_sz_2471_, v___x_2472_, v_a_2470_);
lean_inc_ref(v___y_2454_);
v___x_2474_ = lean_apply_1(v___x_10154__overap_2473_, v___y_2454_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_del_object(v___x_2458_);
lean_dec(v_____do__lift_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; 
v_a_2483_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2474_, 1);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v_a_2483_);
v___x_2485_ = v___x_2458_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
v___y_2403_ = v___y_2447_;
v___y_2404_ = v___y_2449_;
v___y_2405_ = v___y_2448_;
v___y_2406_ = v___y_2450_;
v___y_2407_ = v___y_2451_;
v___y_2408_ = v___y_2452_;
v___y_2409_ = v_____do__lift_2453_;
v_____do__lift_2410_ = v___x_2485_;
v___y_2411_ = v___y_2454_;
goto v___jp_2402_;
}
}
}
}
}
}
v___jp_2489_:
{
lean_object* v_rpcDecode_2496_; lean_object* v___x_2497_; 
v_rpcDecode_2496_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc_ref(v_rpcDecode_2496_);
lean_dec_ref(v_inst_2298_);
lean_inc_ref(v___y_2495_);
v___x_2497_ = lean_apply_2(v_rpcDecode_2496_, v_message_2328_, v___y_2495_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_____do__lift_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
if (lean_obj_tag(v_tags_x3f_2329_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v___f_2488_);
v_a_2506_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2507_ = lean_box(0);
v___y_2447_ = v___y_2490_;
v___y_2448_ = v___y_2492_;
v___y_2449_ = v___y_2491_;
v___y_2450_ = v_a_2506_;
v___y_2451_ = v___y_2493_;
v___y_2452_ = v_____do__lift_2494_;
v_____do__lift_2453_ = v___x_2507_;
v___y_2454_ = v___y_2495_;
goto v___jp_2446_;
}
else
{
lean_object* v_a_2508_; lean_object* v_val_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2540_; 
v_a_2508_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2497_, 1);
v_val_2509_ = lean_ctor_get(v_tags_x3f_2329_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_tags_x3f_2329_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2511_ = v_tags_x3f_2329_;
v_isShared_2512_ = v_isSharedCheck_2540_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_val_2509_);
lean_dec(v_tags_x3f_2329_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2540_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___f_2513_; lean_object* v___x_2514_; 
v___f_2513_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2514_ = l_Lean_Array_fromJson_x3f___redArg(v___f_2513_, v_val_2509_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2511_);
lean_dec(v_a_2508_);
lean_dec(v_____do__lift_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2523_; size_t v_sz_2524_; size_t v___x_2525_; lean_object* v___x_10205__overap_2526_; lean_object* v___x_2527_; 
v_a_2523_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2514_, 1);
v_sz_2524_ = lean_array_size(v_a_2523_);
v___x_2525_ = ((size_t)0ULL);
v___x_10205__overap_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2315_, v___f_2488_, v_sz_2524_, v___x_2525_, v_a_2523_);
lean_inc_ref(v___y_2495_);
v___x_2527_ = lean_apply_1(v___x_10205__overap_2526_, v___y_2495_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_del_object(v___x_2511_);
lean_dec(v_a_2508_);
lean_dec(v_____do__lift_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; 
v_a_2536_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2527_, 1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_a_2536_);
v___x_2538_ = v___x_2511_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
v___y_2447_ = v___y_2490_;
v___y_2448_ = v___y_2492_;
v___y_2449_ = v___y_2491_;
v___y_2450_ = v_a_2508_;
v___y_2451_ = v___y_2493_;
v___y_2452_ = v_____do__lift_2494_;
v_____do__lift_2453_ = v___x_2538_;
v___y_2454_ = v___y_2495_;
goto v___jp_2446_;
}
}
}
}
}
}
}
v___jp_2541_:
{
if (lean_obj_tag(v_source_x3f_2327_) == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_box(0);
v___y_2490_ = v___y_2542_;
v___y_2491_ = v_____do__lift_2545_;
v___y_2492_ = v___y_2543_;
v___y_2493_ = v___y_2544_;
v_____do__lift_2494_ = v___x_2547_;
v___y_2495_ = v___y_2546_;
goto v___jp_2489_;
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2567_; 
v_val_2548_ = lean_ctor_get(v_source_x3f_2327_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_source_x3f_2327_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2550_ = v_source_x3f_2327_;
v_isShared_2551_ = v_isSharedCheck_2567_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_val_2548_);
lean_dec(v_source_x3f_2327_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2567_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_10377__overap_2553_; lean_object* v___x_2554_; 
v___x_2552_ = l_Lean_Json_getStr_x3f(v_val_2548_);
lean_inc_ref(v___x_2321_);
v___x_10377__overap_2553_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2552_);
lean_inc_ref(v___y_2546_);
v___x_2554_ = lean_apply_1(v___x_10377__overap_2553_, v___y_2546_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_del_object(v___x_2550_);
lean_dec(v_____do__lift_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2554_, 1);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v_a_2563_);
v___x_2565_ = v___x_2550_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v___y_2490_ = v___y_2542_;
v___y_2491_ = v_____do__lift_2545_;
v___y_2492_ = v___y_2543_;
v___y_2493_ = v___y_2544_;
v_____do__lift_2494_ = v___x_2565_;
v___y_2495_ = v___y_2546_;
goto v___jp_2489_;
}
}
}
}
}
v___jp_2568_:
{
if (lean_obj_tag(v___y_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec(v_source_x3f_2327_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2574_ = lean_ctor_get(v___y_2573_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___y_2573_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___y_2573_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___y_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2583_; 
v_a_2582_ = lean_ctor_get(v___y_2573_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___y_2573_, 1);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_a_2582_);
v___y_2542_ = v___y_2569_;
v___y_2543_ = v___y_2570_;
v___y_2544_ = v___y_2571_;
v_____do__lift_2545_ = v___x_2583_;
v___y_2546_ = v___y_2572_;
goto v___jp_2541_;
}
}
v___jp_2584_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_10379__overap_2597_; lean_object* v___x_2598_; 
v___x_2590_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2591_ = lean_unsigned_to_nat(80u);
v___x_2592_ = l_Lean_Json_pretty(v_j_2589_, v___x_2591_);
v___x_2593_ = lean_string_append(v___x_2590_, v___x_2592_);
lean_dec_ref(v___x_2592_);
v___x_2594_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2595_ = lean_string_append(v___x_2593_, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_inc_ref(v___x_2321_);
v___x_10379__overap_2597_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2596_);
lean_inc_ref(v___y_2588_);
v___x_2598_ = lean_apply_1(v___x_10379__overap_2597_, v___y_2588_);
v___y_2569_ = v___y_2585_;
v___y_2570_ = v___y_2586_;
v___y_2571_ = v___y_2587_;
v___y_2572_ = v___y_2588_;
v___y_2573_ = v___x_2598_;
goto v___jp_2568_;
}
v___jp_2599_:
{
if (lean_obj_tag(v_code_x3f_2326_) == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_box(0);
v___y_2542_ = v___y_2600_;
v___y_2543_ = v___y_2601_;
v___y_2544_ = v_____do__lift_2602_;
v_____do__lift_2545_ = v___x_2604_;
v___y_2546_ = v___y_2603_;
goto v___jp_2541_;
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2640_; 
v_val_2605_ = lean_ctor_get(v_code_x3f_2326_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_code_x3f_2326_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2607_ = v_code_x3f_2326_;
v_isShared_2608_ = v_isSharedCheck_2640_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_val_2605_);
lean_dec(v_code_x3f_2326_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2640_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
switch(lean_obj_tag(v_val_2605_))
{
case 2:
{
lean_object* v_n_2609_; lean_object* v_mantissa_2610_; lean_object* v_exponent_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_n_2609_ = lean_ctor_get(v_val_2605_, 0);
v_mantissa_2610_ = lean_ctor_get(v_n_2609_, 0);
v_exponent_2611_ = lean_ctor_get(v_n_2609_, 1);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_nat_dec_eq(v_exponent_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_del_object(v___x_2607_);
v___y_2585_ = v___y_2600_;
v___y_2586_ = v___y_2601_;
v___y_2587_ = v_____do__lift_2602_;
v___y_2588_ = v___y_2603_;
v_j_2589_ = v_val_2605_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2625_; 
lean_inc(v_mantissa_2610_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_val_2605_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_val_2605_, 0);
lean_dec(v_unused_2626_);
v___x_2615_ = v_val_2605_;
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
else
{
lean_dec(v_val_2605_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set_tag(v___x_2615_, 0);
lean_ctor_set(v___x_2615_, 0, v_mantissa_2610_);
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_mantissa_2610_);
v___x_2618_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2618_);
v___x_2620_ = v___x_2607_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_10382__overap_2621_; lean_object* v___x_2622_; 
lean_inc_ref(v___x_2321_);
v___x_10382__overap_2621_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2620_);
lean_inc_ref(v___y_2603_);
v___x_2622_ = lean_apply_1(v___x_10382__overap_2621_, v___y_2603_);
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v_____do__lift_2602_;
v___y_2572_ = v___y_2603_;
v___y_2573_ = v___x_2622_;
goto v___jp_2568_;
}
}
}
}
}
case 3:
{
lean_object* v_s_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2639_; 
v_s_2627_ = lean_ctor_get(v_val_2605_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_val_2605_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2629_ = v_val_2605_;
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_s_2627_);
lean_dec(v_val_2605_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 1);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_s_2627_);
v___x_2632_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2632_);
v___x_2634_ = v___x_2607_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_10384__overap_2635_; lean_object* v___x_2636_; 
lean_inc_ref(v___x_2321_);
v___x_10384__overap_2635_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2634_);
lean_inc_ref(v___y_2603_);
v___x_2636_ = lean_apply_1(v___x_10384__overap_2635_, v___y_2603_);
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v_____do__lift_2602_;
v___y_2572_ = v___y_2603_;
v___y_2573_ = v___x_2636_;
goto v___jp_2568_;
}
}
}
}
default: 
{
lean_del_object(v___x_2607_);
v___y_2585_ = v___y_2600_;
v___y_2586_ = v___y_2601_;
v___y_2587_ = v_____do__lift_2602_;
v___y_2588_ = v___y_2603_;
v_j_2589_ = v_val_2605_;
goto v___jp_2584_;
}
}
}
}
}
v___jp_2641_:
{
if (lean_obj_tag(v_isSilent_x3f_2325_) == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_box(0);
v___y_2600_ = v___y_2642_;
v___y_2601_ = v_____do__lift_2643_;
v_____do__lift_2602_ = v___x_2645_;
v___y_2603_ = v___y_2644_;
goto v___jp_2599_;
}
else
{
lean_object* v_val_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2665_; 
v_val_2646_ = lean_ctor_get(v_isSilent_x3f_2325_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_isSilent_x3f_2325_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2648_ = v_isSilent_x3f_2325_;
v_isShared_2649_ = v_isSharedCheck_2665_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_val_2646_);
lean_dec(v_isSilent_x3f_2325_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2665_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_10386__overap_2651_; lean_object* v___x_2652_; 
v___x_2650_ = l_Lean_Json_getBool_x3f(v_val_2646_);
lean_dec(v_val_2646_);
lean_inc_ref(v___x_2321_);
v___x_10386__overap_2651_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2650_);
lean_inc_ref(v___y_2644_);
v___x_2652_ = lean_apply_1(v___x_10386__overap_2651_, v___y_2644_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_del_object(v___x_2648_);
lean_dec(v_____do__lift_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec(v_source_x3f_2327_);
lean_dec(v_code_x3f_2326_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; 
v_a_2661_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2652_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_a_2661_);
v___x_2663_ = v___x_2648_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
v___y_2600_ = v___y_2642_;
v___y_2601_ = v_____do__lift_2643_;
v_____do__lift_2602_ = v___x_2663_;
v___y_2603_ = v___y_2644_;
goto v___jp_2599_;
}
}
}
}
}
v___jp_2666_:
{
if (lean_obj_tag(v___y_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v___y_2667_);
lean_dec_ref(v___f_2488_);
lean_dec_ref(v___f_2445_);
lean_dec_ref(v___f_2401_);
lean_del_object(v___x_2349_);
lean_dec(v_a_2347_);
lean_del_object(v___x_2334_);
lean_dec(v_data_x3f_2332_);
lean_dec(v_relatedInformation_x3f_2331_);
lean_dec(v_leanTags_x3f_2330_);
lean_dec(v_tags_x3f_2329_);
lean_dec(v_message_2328_);
lean_dec(v_source_x3f_2327_);
lean_dec(v_code_x3f_2326_);
lean_dec(v_isSilent_x3f_2325_);
lean_dec_ref(v___x_2321_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_inst_2298_);
v_a_2670_ = lean_ctor_get(v___y_2669_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___y_2669_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___y_2669_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___y_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___y_2669_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___y_2669_, 1);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_a_2678_);
v___y_2642_ = v___y_2667_;
v_____do__lift_2643_ = v___x_2679_;
v___y_2644_ = v___y_2668_;
goto v___jp_2641_;
}
}
v___jp_2680_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_10388__overap_2691_; lean_object* v___x_2692_; 
v___x_2684_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2685_ = lean_unsigned_to_nat(80u);
v___x_2686_ = l_Lean_Json_pretty(v___y_2683_, v___x_2685_);
v___x_2687_ = lean_string_append(v___x_2684_, v___x_2686_);
lean_dec_ref(v___x_2686_);
v___x_2688_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2689_ = lean_string_append(v___x_2687_, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_inc_ref(v___x_2321_);
v___x_10388__overap_2691_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2690_);
lean_inc_ref(v___y_2682_);
v___x_2692_ = lean_apply_1(v___x_10388__overap_2691_, v___y_2682_);
v___y_2667_ = v___y_2681_;
v___y_2668_ = v___y_2682_;
v___y_2669_ = v___x_2692_;
goto v___jp_2666_;
}
v___jp_2693_:
{
if (lean_obj_tag(v_severity_x3f_2324_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_box(0);
v___y_2642_ = v_____do__lift_2694_;
v_____do__lift_2643_ = v___x_2696_;
v___y_2644_ = v___y_2695_;
goto v___jp_2641_;
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2698_; 
v_val_2697_ = lean_ctor_get(v_severity_x3f_2324_, 0);
lean_inc_n(v_val_2697_, 2);
lean_dec_ref_known(v_severity_x3f_2324_, 1);
v___x_2698_ = l_Lean_Json_getNat_x3f(v_val_2697_);
if (lean_obj_tag(v___x_2698_) == 1)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_dec_eq(v_a_2699_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = lean_unsigned_to_nat(2u);
v___x_2703_ = lean_nat_dec_eq(v_a_2699_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = lean_unsigned_to_nat(3u);
v___x_2705_ = lean_nat_dec_eq(v_a_2699_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(4u);
v___x_2707_ = lean_nat_dec_eq(v_a_2699_, v___x_2706_);
lean_dec(v_a_2699_);
if (v___x_2707_ == 0)
{
v___y_2681_ = v_____do__lift_2694_;
v___y_2682_ = v___y_2695_;
v___y_2683_ = v_val_2697_;
goto v___jp_2680_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_10394__overap_2709_; lean_object* v___x_2710_; 
lean_dec(v_val_2697_);
v___x_2708_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2321_);
v___x_10394__overap_2709_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2708_);
lean_inc_ref(v___y_2695_);
v___x_2710_ = lean_apply_1(v___x_10394__overap_2709_, v___y_2695_);
v___y_2667_ = v_____do__lift_2694_;
v___y_2668_ = v___y_2695_;
v___y_2669_ = v___x_2710_;
goto v___jp_2666_;
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_10396__overap_2712_; lean_object* v___x_2713_; 
lean_dec(v_a_2699_);
lean_dec(v_val_2697_);
v___x_2711_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2321_);
v___x_10396__overap_2712_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2711_);
lean_inc_ref(v___y_2695_);
v___x_2713_ = lean_apply_1(v___x_10396__overap_2712_, v___y_2695_);
v___y_2667_ = v_____do__lift_2694_;
v___y_2668_ = v___y_2695_;
v___y_2669_ = v___x_2713_;
goto v___jp_2666_;
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_10398__overap_2715_; lean_object* v___x_2716_; 
lean_dec(v_a_2699_);
lean_dec(v_val_2697_);
v___x_2714_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2321_);
v___x_10398__overap_2715_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2714_);
lean_inc_ref(v___y_2695_);
v___x_2716_ = lean_apply_1(v___x_10398__overap_2715_, v___y_2695_);
v___y_2667_ = v_____do__lift_2694_;
v___y_2668_ = v___y_2695_;
v___y_2669_ = v___x_2716_;
goto v___jp_2666_;
}
}
else
{
lean_object* v___x_2717_; lean_object* v___x_10400__overap_2718_; lean_object* v___x_2719_; 
lean_dec(v_a_2699_);
lean_dec(v_val_2697_);
v___x_2717_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2321_);
v___x_10400__overap_2718_ = l_MonadExcept_ofExcept___redArg(v___x_2315_, v___x_2321_, v___x_2717_);
lean_inc_ref(v___y_2695_);
v___x_2719_ = lean_apply_1(v___x_10400__overap_2718_, v___y_2695_);
v___y_2667_ = v_____do__lift_2694_;
v___y_2668_ = v___y_2695_;
v___y_2669_ = v___x_2719_;
goto v___jp_2666_;
}
}
else
{
lean_dec_ref(v___x_2698_);
v___y_2681_ = v_____do__lift_2694_;
v___y_2682_ = v___y_2695_;
v___y_2683_ = v_val_2697_;
goto v___jp_2680_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_inst_2744_, lean_object* v_j_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2744_, v_j_2745_, v_a_2746_);
lean_dec_ref(v_a_2746_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2748_, lean_object* v_inst_2749_, lean_object* v_j_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2749_, v_j_2750_, v_a_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_00_u03b1_2753_, lean_object* v_inst_2754_, lean_object* v_j_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_00_u03b1_2753_, v_inst_2754_, v_j_2755_, v_a_2756_);
lean_dec_ref(v_a_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object* v_inst_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_inc_ref(v_inst_2758_);
v___x_2759_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___x_2759_, 0, lean_box(0));
lean_closure_set(v___x_2759_, 1, v_inst_2758_);
v___x_2760_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___x_2760_, 0, lean_box(0));
lean_closure_set(v___x_2760_, 1, v_inst_2758_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object* v_00_u03b1_2762_, lean_object* v_inst_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(v_inst_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
switch(lean_obj_tag(v_x_2768_))
{
case 0:
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2778_; 
v_a_2770_ = lean_ctor_get(v_x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2772_ = v_x_2768_;
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v_x_2768_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_a_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
case 1:
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2790_; 
v_a_2779_ = lean_ctor_get(v_x_2768_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2768_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2781_ = v_x_2768_;
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v_x_2768_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2783_ = l_Lean_Widget_InteractiveGoal_pretty(v_a_2779_);
v___x_2784_ = l_Std_Format_defWidth;
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = l_Std_Format_pretty(v___x_2783_, v___x_2784_, v___x_2785_, v___x_2785_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2786_);
v___x_2788_ = v___x_2781_;
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
case 2:
{
lean_object* v_alt_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_alt_2791_ = lean_ctor_get(v_x_2768_, 1);
lean_inc_ref(v_alt_2791_);
lean_dec_ref_known(v_x_2768_, 2);
v___x_2792_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_alt_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
default: 
{
lean_object* v___x_2794_; 
lean_dec_ref_known(v_x_2768_, 4);
v___x_2794_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1));
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object* v_x_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(v_x_2795_, v_x_2796_);
lean_dec_ref(v_x_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object* v_tt_2798_){
_start:
{
lean_object* v___f_2799_; lean_object* v_tt_2800_; lean_object* v___x_2801_; 
v___f_2799_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed), 2, 0);
v_tt_2800_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_2799_, v_tt_2798_);
v___x_2801_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object* v_diag_2802_){
_start:
{
lean_object* v_range_2803_; lean_object* v_fullRange_x3f_2804_; lean_object* v_severity_x3f_2805_; lean_object* v_isSilent_x3f_2806_; lean_object* v_code_x3f_2807_; lean_object* v_source_x3f_2808_; lean_object* v_message_2809_; lean_object* v_tags_x3f_2810_; lean_object* v_leanTags_x3f_2811_; lean_object* v_relatedInformation_x3f_2812_; lean_object* v_data_x3f_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2821_; 
v_range_2803_ = lean_ctor_get(v_diag_2802_, 0);
v_fullRange_x3f_2804_ = lean_ctor_get(v_diag_2802_, 1);
v_severity_x3f_2805_ = lean_ctor_get(v_diag_2802_, 2);
v_isSilent_x3f_2806_ = lean_ctor_get(v_diag_2802_, 3);
v_code_x3f_2807_ = lean_ctor_get(v_diag_2802_, 4);
v_source_x3f_2808_ = lean_ctor_get(v_diag_2802_, 5);
v_message_2809_ = lean_ctor_get(v_diag_2802_, 6);
v_tags_x3f_2810_ = lean_ctor_get(v_diag_2802_, 7);
v_leanTags_x3f_2811_ = lean_ctor_get(v_diag_2802_, 8);
v_relatedInformation_x3f_2812_ = lean_ctor_get(v_diag_2802_, 9);
v_data_x3f_2813_ = lean_ctor_get(v_diag_2802_, 10);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_diag_2802_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2815_ = v_diag_2802_;
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_data_x3f_2813_);
lean_inc(v_relatedInformation_x3f_2812_);
lean_inc(v_leanTags_x3f_2811_);
lean_inc(v_tags_x3f_2810_);
lean_inc(v_message_2809_);
lean_inc(v_source_x3f_2808_);
lean_inc(v_code_x3f_2807_);
lean_inc(v_isSilent_x3f_2806_);
lean_inc(v_severity_x3f_2805_);
lean_inc(v_fullRange_x3f_2804_);
lean_inc(v_range_2803_);
lean_dec(v_diag_2802_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2817_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_message_2809_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 6, v___x_2817_);
v___x_2819_ = v___x_2815_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_range_2803_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_fullRange_x3f_2804_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_severity_x3f_2805_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v_isSilent_x3f_2806_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v_code_x3f_2807_);
lean_ctor_set(v_reuseFailAlloc_2820_, 5, v_source_x3f_2808_);
lean_ctor_set(v_reuseFailAlloc_2820_, 6, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2820_, 7, v_tags_x3f_2810_);
lean_ctor_set(v_reuseFailAlloc_2820_, 8, v_leanTags_x3f_2811_);
lean_ctor_set(v_reuseFailAlloc_2820_, 9, v_relatedInformation_x3f_2812_);
lean_ctor_set(v_reuseFailAlloc_2820_, 10, v_data_x3f_2813_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object* v_nCtx_2822_, lean_object* v_ctx_2823_){
_start:
{
lean_object* v_env_2824_; lean_object* v_mctx_2825_; lean_object* v_lctx_2826_; lean_object* v_opts_2827_; lean_object* v_currNamespace_2828_; lean_object* v_openDecls_2829_; lean_object* v___x_2830_; 
v_env_2824_ = lean_ctor_get(v_ctx_2823_, 0);
v_mctx_2825_ = lean_ctor_get(v_ctx_2823_, 1);
v_lctx_2826_ = lean_ctor_get(v_ctx_2823_, 2);
v_opts_2827_ = lean_ctor_get(v_ctx_2823_, 3);
v_currNamespace_2828_ = lean_ctor_get(v_nCtx_2822_, 0);
v_openDecls_2829_ = lean_ctor_get(v_nCtx_2822_, 1);
lean_inc(v_openDecls_2829_);
lean_inc(v_currNamespace_2828_);
lean_inc_ref(v_opts_2827_);
lean_inc_ref(v_lctx_2826_);
lean_inc_ref(v_mctx_2825_);
lean_inc_ref(v_env_2824_);
v___x_2830_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2830_, 0, v_env_2824_);
lean_ctor_set(v___x_2830_, 1, v_mctx_2825_);
lean_ctor_set(v___x_2830_, 2, v_lctx_2826_);
lean_ctor_set(v___x_2830_, 3, v_opts_2827_);
lean_ctor_set(v___x_2830_, 4, v_currNamespace_2828_);
lean_ctor_set(v___x_2830_, 5, v_openDecls_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object* v_nCtx_2831_, lean_object* v_ctx_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_2831_, v_ctx_2832_);
lean_dec_ref(v_ctx_2832_);
lean_dec_ref(v_nCtx_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl(lean_object* v_x_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_obj_tag_nat(v_x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl___boxed(lean_object* v_x_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___impl(v_x_2836_);
lean_dec(v_x_2836_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(lean_object* v_t_2838_, lean_object* v_k_2839_){
_start:
{
switch(lean_obj_tag(v_t_2838_))
{
case 1:
{
lean_object* v_ctx_2840_; lean_object* v_lctx_2841_; lean_object* v_g_2842_; lean_object* v___x_2843_; 
v_ctx_2840_ = lean_ctor_get(v_t_2838_, 0);
lean_inc_ref(v_ctx_2840_);
v_lctx_2841_ = lean_ctor_get(v_t_2838_, 1);
lean_inc_ref(v_lctx_2841_);
v_g_2842_ = lean_ctor_get(v_t_2838_, 2);
lean_inc(v_g_2842_);
lean_dec_ref_known(v_t_2838_, 3);
v___x_2843_ = lean_apply_3(v_k_2839_, v_ctx_2840_, v_lctx_2841_, v_g_2842_);
return v___x_2843_;
}
case 3:
{
lean_object* v_cls_2844_; lean_object* v_msg_2845_; uint8_t v_collapsed_2846_; lean_object* v_children_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_cls_2844_ = lean_ctor_get(v_t_2838_, 0);
lean_inc(v_cls_2844_);
v_msg_2845_ = lean_ctor_get(v_t_2838_, 1);
lean_inc(v_msg_2845_);
v_collapsed_2846_ = lean_ctor_get_uint8(v_t_2838_, sizeof(void*)*3);
v_children_2847_ = lean_ctor_get(v_t_2838_, 2);
lean_inc_ref(v_children_2847_);
lean_dec_ref_known(v_t_2838_, 3);
v___x_2848_ = lean_box(v_collapsed_2846_);
v___x_2849_ = lean_apply_4(v_k_2839_, v_cls_2844_, v_msg_2845_, v___x_2848_, v_children_2847_);
return v___x_2849_;
}
case 4:
{
return v_k_2839_;
}
default: 
{
lean_object* v_ctx_2850_; lean_object* v_infos_2851_; lean_object* v___x_2852_; 
v_ctx_2850_ = lean_ctor_get(v_t_2838_, 0);
lean_inc_ref(v_ctx_2850_);
v_infos_2851_ = lean_ctor_get(v_t_2838_, 1);
lean_inc(v_infos_2851_);
lean_dec(v_t_2838_);
v___x_2852_ = lean_apply_2(v_k_2839_, v_ctx_2850_, v_infos_2851_);
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(lean_object* v_motive_2853_, lean_object* v_ctorIdx_2854_, lean_object* v_t_2855_, lean_object* v_h_2856_, lean_object* v_k_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2855_, v_k_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___boxed(lean_object* v_motive_2859_, lean_object* v_ctorIdx_2860_, lean_object* v_t_2861_, lean_object* v_h_2862_, lean_object* v_k_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(v_motive_2859_, v_ctorIdx_2860_, v_t_2861_, v_h_2862_, v_k_2863_);
lean_dec(v_ctorIdx_2860_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim___redArg(lean_object* v_t_2865_, lean_object* v_code_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2865_, v_code_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim(lean_object* v_motive_2868_, lean_object* v_t_2869_, lean_object* v_h_2870_, lean_object* v_code_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2869_, v_code_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim___redArg(lean_object* v_t_2873_, lean_object* v_goal_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2873_, v_goal_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim(lean_object* v_motive_2876_, lean_object* v_t_2877_, lean_object* v_h_2878_, lean_object* v_goal_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2877_, v_goal_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim___redArg(lean_object* v_t_2881_, lean_object* v_widget_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2881_, v_widget_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim(lean_object* v_motive_2884_, lean_object* v_t_2885_, lean_object* v_h_2886_, lean_object* v_widget_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2885_, v_widget_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim___redArg(lean_object* v_t_2889_, lean_object* v_trace_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2889_, v_trace_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim(lean_object* v_motive_2892_, lean_object* v_t_2893_, lean_object* v_h_2894_, lean_object* v_trace_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2893_, v_trace_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim___redArg(lean_object* v_t_2897_, lean_object* v_ignoreTags_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2897_, v_ignoreTags_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim(lean_object* v_motive_2900_, lean_object* v_t_2901_, lean_object* v_h_2902_, lean_object* v_ignoreTags_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2901_, v_ignoreTags_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0(void){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Array_instInhabited___redArg();
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__0);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2(void){
_start:
{
lean_object* v___x_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2908_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__1);
v___x_2909_ = 0;
v___x_2910_ = lean_box(0);
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2910_);
lean_ctor_set(v___x_2912_, 2, v___x_2908_);
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*3, v___x_2909_);
return v___x_2912_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedEmbedFmt_default(void){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_obj_once(&l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2, &l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2_once, _init_l_Lean_Widget_instInhabitedEmbedFmt_default___closed__2);
return v___x_2913_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt(void){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Widget_instInhabitedEmbedFmt_default;
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object* v_e_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2918_ = lean_array_get_size(v_a_2916_);
v___x_2919_ = lean_array_push(v_a_2916_, v_e_2915_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed___boxed(lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v_e_2922_, v_a_2923_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object* v_fmt_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2948_; 
v___x_2929_ = lean_box(4);
v___x_2930_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_2929_, v_a_2927_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2948_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2948_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_fst_2935_; lean_object* v_snd_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2947_; 
v_fst_2935_ = lean_ctor_get(v_a_2931_, 0);
v_snd_2936_ = lean_ctor_get(v_a_2931_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2931_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2938_ = v_a_2931_;
v_isShared_2939_ = v_isSharedCheck_2947_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_snd_2936_);
lean_inc(v_fst_2935_);
lean_dec(v_a_2931_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2947_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_fst_2935_);
lean_ctor_set(v___x_2940_, 1, v_fmt_2926_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_snd_2936_);
v___x_2942_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2944_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2942_);
v___x_2944_ = v___x_2933_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags___boxed(lean_object* v_fmt_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_2949_, v_a_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object* v_nCtx_2961_, lean_object* v_ctx_2962_){
_start:
{
lean_object* v_env_2963_; lean_object* v_mctx_2964_; lean_object* v_opts_2965_; lean_object* v_currNamespace_2966_; lean_object* v_openDecls_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_env_2963_ = lean_ctor_get(v_ctx_2962_, 0);
v_mctx_2964_ = lean_ctor_get(v_ctx_2962_, 1);
v_opts_2965_ = lean_ctor_get(v_ctx_2962_, 3);
v_currNamespace_2966_ = lean_ctor_get(v_nCtx_2961_, 0);
v_openDecls_2967_ = lean_ctor_get(v_nCtx_2961_, 1);
v___x_2968_ = lean_box(0);
v___x_2969_ = l_Lean_instInhabitedFileMap_default;
v___x_2970_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2));
lean_inc(v_openDecls_2967_);
lean_inc(v_currNamespace_2966_);
lean_inc_ref(v_opts_2965_);
lean_inc_ref(v_mctx_2964_);
lean_inc_ref(v_env_2963_);
v___x_2971_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2971_, 0, v_env_2963_);
lean_ctor_set(v___x_2971_, 1, v___x_2968_);
lean_ctor_set(v___x_2971_, 2, v___x_2969_);
lean_ctor_set(v___x_2971_, 3, v_mctx_2964_);
lean_ctor_set(v___x_2971_, 4, v_opts_2965_);
lean_ctor_set(v___x_2971_, 5, v_currNamespace_2966_);
lean_ctor_set(v___x_2971_, 6, v_openDecls_2967_);
lean_ctor_set(v___x_2971_, 7, v___x_2970_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3));
v___x_2973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2968_);
lean_ctor_set(v___x_2973_, 2, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object* v_nCtx_2974_, lean_object* v_ctx_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_2974_, v_ctx_2975_);
lean_dec_ref(v_ctx_2975_);
lean_dec_ref(v_nCtx_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(lean_object* v_a_2977_, lean_object* v_b_2978_){
_start:
{
lean_object* v_array_2979_; lean_object* v_start_2980_; lean_object* v_stop_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2994_; 
v_array_2979_ = lean_ctor_get(v_a_2977_, 0);
v_start_2980_ = lean_ctor_get(v_a_2977_, 1);
v_stop_2981_ = lean_ctor_get(v_a_2977_, 2);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_a_2977_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2983_ = v_a_2977_;
v_isShared_2984_ = v_isSharedCheck_2994_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_stop_2981_);
lean_inc(v_start_2980_);
lean_inc(v_array_2979_);
lean_dec(v_a_2977_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2994_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_lt(v_start_2980_, v_stop_2981_);
if (v___x_2985_ == 0)
{
lean_del_object(v___x_2983_);
lean_dec(v_stop_2981_);
lean_dec(v_start_2980_);
lean_dec_ref(v_array_2979_);
return v_b_2978_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = lean_nat_add(v_start_2980_, v___x_2986_);
lean_inc_ref(v_array_2979_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_2987_);
v___x_2989_ = v___x_2983_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_array_2979_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_stop_2981_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_array_fget(v_array_2979_, v_start_2980_);
lean_dec(v_start_2980_);
lean_dec_ref(v_array_2979_);
v___x_2991_ = lean_array_push(v_b_2978_, v___x_2990_);
v_a_2977_ = v___x_2989_;
v_b_2978_ = v___x_2991_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1(void){
_start:
{
lean_object* v___x_2997_; double v___x_2998_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_float_of_nat(v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object* v_cls_3003_, lean_object* v_blockSize_3004_, lean_object* v_children_3005_){
_start:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_nat_dec_lt(v___x_3006_, v_blockSize_3004_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v_cls_3003_);
v___x_3008_ = l_Subarray_copy___redArg(v_children_3005_);
return v___x_3008_;
}
else
{
lean_object* v_start_3009_; lean_object* v_stop_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_start_3009_ = lean_ctor_get(v_children_3005_, 1);
v_stop_3010_ = lean_ctor_get(v_children_3005_, 2);
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_nat_add(v_blockSize_3004_, v___x_3011_);
v___x_3013_ = lean_nat_sub(v_stop_3010_, v_start_3009_);
v___x_3014_ = lean_nat_dec_lt(v___x_3012_, v___x_3013_);
lean_dec(v___x_3012_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
lean_dec(v___x_3013_);
lean_dec(v_cls_3003_);
v___x_3015_ = l_Subarray_copy___redArg(v_children_3005_);
return v___x_3015_;
}
else
{
lean_object* v___x_3016_; lean_object* v_more_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; double v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_inc_ref(v_children_3005_);
v___x_3016_ = l_Subarray_drop___redArg(v_children_3005_, v_blockSize_3004_);
lean_inc(v_cls_3003_);
v_more_3017_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3003_, v_blockSize_3004_, v___x_3016_);
v___x_3018_ = l_Subarray_take___redArg(v_children_3005_, v_blockSize_3004_);
v___x_3019_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0));
v___x_3020_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v___x_3018_, v___x_3019_);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3023_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2));
v___x_3024_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3024_, 0, v_cls_3003_);
lean_ctor_set(v___x_3024_, 1, v___x_3021_);
lean_ctor_set(v___x_3024_, 2, v___x_3023_);
lean_ctor_set_float(v___x_3024_, sizeof(void*)*3, v___x_3022_);
lean_ctor_set_float(v___x_3024_, sizeof(void*)*3 + 8, v___x_3022_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*3 + 16, v___x_3007_);
v___x_3025_ = lean_nat_sub(v___x_3013_, v_blockSize_3004_);
lean_dec(v___x_3013_);
v___x_3026_ = l_Nat_reprFast(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4));
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_MessageData_ofFormat(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3024_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
lean_ctor_set(v___x_3031_, 2, v_more_3017_);
v___x_3032_ = lean_array_push(v___x_3020_, v___x_3031_);
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object* v_cls_3033_, lean_object* v_blockSize_3034_, lean_object* v_children_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3033_, v_blockSize_3034_, v_children_3035_);
lean_dec(v_blockSize_3034_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0(lean_object* v_inst_3037_, lean_object* v_R_3038_, lean_object* v_a_3039_, lean_object* v_b_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v_a_3039_, v_b_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object* v_a_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_nat_to_int(v_a_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object* v_opts_3044_, lean_object* v_opt_3045_){
_start:
{
lean_object* v_name_3046_; lean_object* v_map_3047_; lean_object* v___x_3048_; 
v_name_3046_ = lean_ctor_get(v_opt_3045_, 0);
v_map_3047_ = lean_ctor_get(v_opts_3044_, 0);
v___x_3048_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3047_, v_name_3046_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_box(0);
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3059_; 
v_val_3050_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3052_ = v___x_3048_;
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_val_3050_);
lean_dec(v___x_3048_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
if (lean_obj_tag(v_val_3050_) == 3)
{
lean_object* v_v_3054_; lean_object* v___x_3056_; 
v_v_3054_ = lean_ctor_get(v_val_3050_, 0);
lean_inc(v_v_3054_);
lean_dec_ref_known(v_val_3050_, 1);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v_v_3054_);
v___x_3056_ = v___x_3052_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_v_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_object* v___x_3058_; 
lean_del_object(v___x_3052_);
lean_dec(v_val_3050_);
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object* v_opts_3060_, lean_object* v_opt_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3060_, v_opt_3061_);
lean_dec_ref(v_opt_3061_);
lean_dec_ref(v_opts_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object* v_ctx_3063_, lean_object* v_nCtx_3064_, size_t v_sz_3065_, size_t v_i_3066_, lean_object* v_bs_3067_){
_start:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_usize_dec_lt(v_i_3066_, v_sz_3065_);
if (v___x_3068_ == 0)
{
lean_dec_ref(v_nCtx_3064_);
return v_bs_3067_;
}
else
{
lean_object* v_v_3069_; lean_object* v___x_3070_; lean_object* v_bs_x27_3071_; lean_object* v___y_3073_; 
v_v_3069_ = lean_array_uget(v_bs_3067_, v_i_3066_);
v___x_3070_ = lean_unsigned_to_nat(0u);
v_bs_x27_3071_ = lean_array_uset(v_bs_3067_, v_i_3066_, v___x_3070_);
if (lean_obj_tag(v_ctx_3063_) == 0)
{
lean_object* v___x_3078_; 
lean_inc_ref(v_nCtx_3064_);
v___x_3078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3078_, 0, v_nCtx_3064_);
lean_ctor_set(v___x_3078_, 1, v_v_3069_);
v___y_3073_ = v___x_3078_;
goto v___jp_3072_;
}
else
{
lean_object* v_val_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_val_3079_ = lean_ctor_get(v_ctx_3063_, 0);
lean_inc(v_val_3079_);
v___x_3080_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3080_, 0, v_val_3079_);
lean_ctor_set(v___x_3080_, 1, v_v_3069_);
lean_inc_ref(v_nCtx_3064_);
v___x_3081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_nCtx_3064_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___y_3073_ = v___x_3081_;
goto v___jp_3072_;
}
v___jp_3072_:
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((size_t)1ULL);
v___x_3075_ = lean_usize_add(v_i_3066_, v___x_3074_);
v___x_3076_ = lean_array_uset(v_bs_x27_3071_, v_i_3066_, v___y_3073_);
v_i_3066_ = v___x_3075_;
v_bs_3067_ = v___x_3076_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object* v_ctx_3082_, lean_object* v_nCtx_3083_, lean_object* v_sz_3084_, lean_object* v_i_3085_, lean_object* v_bs_3086_){
_start:
{
size_t v_sz_boxed_3087_; size_t v_i_boxed_3088_; lean_object* v_res_3089_; 
v_sz_boxed_3087_ = lean_unbox_usize(v_sz_3084_);
lean_dec(v_sz_3084_);
v_i_boxed_3088_ = lean_unbox_usize(v_i_3085_);
lean_dec(v_i_3085_);
v_res_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v_ctx_3082_, v_nCtx_3083_, v_sz_boxed_3087_, v_i_boxed_3088_, v_bs_3086_);
lean_dec(v_ctx_3082_);
return v_res_3089_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_unsigned_to_nat(4u);
v___x_3097_ = lean_nat_to_int(v___x_3096_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7));
v___x_3103_ = lean_mk_io_user_error(v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object* v_nCtx_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
uint8_t v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v_nodes_3116_; lean_object* v___y_3117_; uint8_t v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; uint8_t v___y_3206_; uint8_t v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v_header_3211_; lean_object* v___y_3212_; uint8_t v___y_3217_; double v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; double v___y_3225_; uint8_t v___y_3235_; double v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; double v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v_ctx_3247_; lean_object* v_data_3248_; lean_object* v_header_3249_; lean_object* v_children_3250_; lean_object* v___y_3251_; lean_object* v_ctx_3314_; lean_object* v_n_3315_; lean_object* v_d_3316_; lean_object* v___y_3317_; lean_object* v_ctx_3339_; lean_object* v_wi_3340_; lean_object* v_d_3341_; lean_object* v___y_3342_; lean_object* v_ctx_3383_; lean_object* v_d_3384_; lean_object* v___y_3385_; lean_object* v_ctx_3389_; lean_object* v_d_u2081_3390_; lean_object* v_d_u2082_3391_; lean_object* v___y_3392_; lean_object* v_ctx_3423_; lean_object* v_d_3424_; lean_object* v___y_3425_; lean_object* v___x_3446_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; 
v___x_3446_ = l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_;
if (lean_obj_tag(v_a_3108_) == 0)
{
switch(lean_obj_tag(v_a_3109_))
{
case 0:
{
lean_object* v_a_3458_; lean_object* v_fmt_3459_; lean_object* v___x_3460_; 
lean_dec_ref(v_nCtx_3107_);
v_a_3458_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3458_);
lean_dec_ref_known(v_a_3109_, 1);
v_fmt_3459_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_fmt_3459_);
lean_dec_ref(v_a_3458_);
v___x_3460_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_3459_, v_a_3110_);
return v___x_3460_;
}
case 1:
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v_nCtx_3107_);
v_a_3461_ = lean_ctor_get(v_a_3109_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_a_3109_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3463_ = v_a_3109_;
v_isShared_3464_ = v_isSharedCheck_3474_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v_a_3109_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3474_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3465_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__10));
v___x_3466_ = l_Lean_mkMVar(v_a_3461_);
v___x_3467_ = lean_expr_dbg_to_string(v___x_3466_);
lean_dec_ref(v___x_3466_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set_tag(v___x_3463_, 3);
lean_ctor_set(v___x_3463_, 0, v___x_3467_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3465_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_a_3110_);
v___x_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
return v___x_3472_;
}
}
}
case 2:
{
lean_object* v_a_3475_; lean_object* v_a_3476_; 
v_a_3475_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3475_);
v_a_3476_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3476_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3339_ = v_a_3108_;
v_wi_3340_ = v_a_3475_;
v_d_3341_ = v_a_3476_;
v___y_3342_ = v_a_3110_;
goto v___jp_3338_;
}
case 3:
{
lean_object* v_a_3477_; lean_object* v_a_3478_; 
v_a_3477_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3477_);
v_a_3478_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3478_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3383_ = v_a_3477_;
v_d_3384_ = v_a_3478_;
v___y_3385_ = v_a_3110_;
goto v___jp_3382_;
}
case 4:
{
lean_object* v_a_3479_; lean_object* v_a_3480_; 
lean_dec_ref(v_nCtx_3107_);
v_a_3479_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3479_);
v_a_3480_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3480_);
lean_dec_ref_known(v_a_3109_, 2);
v_nCtx_3107_ = v_a_3479_;
v_a_3109_ = v_a_3480_;
goto _start;
}
case 5:
{
lean_object* v_a_3482_; lean_object* v_a_3483_; 
v_a_3482_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_a_3482_);
v_a_3483_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3483_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3314_ = v_a_3108_;
v_n_3315_ = v_a_3482_;
v_d_3316_ = v_a_3483_;
v___y_3317_ = v_a_3110_;
goto v___jp_3313_;
}
case 6:
{
lean_object* v_a_3484_; 
v_a_3484_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3484_);
lean_dec_ref_known(v_a_3109_, 1);
v_ctx_3423_ = v_a_3108_;
v_d_3424_ = v_a_3484_;
v___y_3425_ = v_a_3110_;
goto v___jp_3422_;
}
case 7:
{
lean_object* v_a_3485_; lean_object* v_a_3486_; 
v_a_3485_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3485_);
v_a_3486_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3486_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3389_ = v_a_3108_;
v_d_u2081_3390_ = v_a_3485_;
v_d_u2082_3391_ = v_a_3486_;
v___y_3392_ = v_a_3110_;
goto v___jp_3388_;
}
case 9:
{
lean_object* v_data_3487_; lean_object* v_msg_3488_; lean_object* v_children_3489_; 
v_data_3487_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_data_3487_);
v_msg_3488_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_msg_3488_);
v_children_3489_ = lean_ctor_get(v_a_3109_, 2);
lean_inc_ref(v_children_3489_);
lean_dec_ref_known(v_a_3109_, 3);
v_ctx_3247_ = v_a_3108_;
v_data_3248_ = v_data_3487_;
v_header_3249_ = v_msg_3488_;
v_children_3250_ = v_children_3489_;
v___y_3251_ = v_a_3110_;
goto v___jp_3246_;
}
case 10:
{
lean_object* v_f_3490_; lean_object* v___x_3491_; 
v_f_3490_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_f_3490_);
lean_dec_ref_known(v_a_3109_, 2);
v___x_3491_ = lean_box(0);
v___y_3448_ = v_f_3490_;
v___y_3449_ = v_a_3110_;
v___y_3450_ = v_a_3108_;
v___y_3451_ = v___x_3491_;
goto v___jp_3447_;
}
default: 
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3492_);
lean_dec_ref(v_a_3109_);
v_a_3109_ = v_a_3492_;
goto _start;
}
}
}
else
{
switch(lean_obj_tag(v_a_3109_))
{
case 0:
{
lean_object* v_a_3494_; lean_object* v_val_3495_; lean_object* v_fmt_3496_; lean_object* v_infos_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3532_; 
v_a_3494_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3494_);
lean_dec_ref_known(v_a_3109_, 1);
v_val_3495_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_val_3495_);
lean_dec_ref_known(v_a_3108_, 1);
v_fmt_3496_ = lean_ctor_get(v_a_3494_, 0);
v_infos_3497_ = lean_ctor_get(v_a_3494_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3494_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3499_ = v_a_3494_;
v_isShared_3500_ = v_isSharedCheck_3532_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_infos_3497_);
lean_inc(v_fmt_3496_);
lean_dec(v_a_3494_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3532_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3501_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3107_, v_val_3495_);
lean_dec(v_val_3495_);
lean_dec_ref(v_nCtx_3107_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3501_);
v___x_3503_ = v___x_3499_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_infos_3497_);
v___x_3503_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; 
v___x_3504_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3503_, v_a_3110_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3522_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3522_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3522_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v_fst_3509_; lean_object* v_snd_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3521_; 
v_fst_3509_ = lean_ctor_get(v_a_3505_, 0);
v_snd_3510_ = lean_ctor_get(v_a_3505_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3505_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3512_ = v_a_3505_;
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_snd_3510_);
lean_inc(v_fst_3509_);
lean_dec(v_a_3505_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3514_, 0, v_fst_3509_);
lean_ctor_set(v___x_3514_, 1, v_fmt_3496_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_snd_3510_);
v___x_3516_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3516_);
v___x_3518_ = v___x_3507_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_fmt_3496_);
v_a_3523_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3504_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3504_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
case 1:
{
lean_object* v_val_3533_; lean_object* v_a_3534_; lean_object* v_lctx_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_val_3533_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_val_3533_);
lean_dec_ref_known(v_a_3108_, 1);
v_a_3534_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v_a_3109_, 1);
v_lctx_3535_ = lean_ctor_get(v_val_3533_, 2);
lean_inc_ref(v_lctx_3535_);
v___x_3536_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3107_, v_val_3533_);
lean_dec(v_val_3533_);
lean_dec_ref(v_nCtx_3107_);
v___x_3537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_lctx_3535_);
lean_ctor_set(v___x_3537_, 2, v_a_3534_);
v___x_3538_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3537_, v_a_3110_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3557_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3557_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3557_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3556_; 
v_fst_3543_ = lean_ctor_get(v_a_3539_, 0);
v_snd_3544_ = lean_ctor_get(v_a_3539_, 1);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_a_3539_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3546_ = v_a_3539_;
v_isShared_3547_ = v_isSharedCheck_3556_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_snd_3544_);
lean_inc(v_fst_3543_);
lean_dec(v_a_3539_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3556_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_fst_3543_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3549_);
v___x_3551_ = v___x_3546_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_snd_3544_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3551_);
v___x_3553_ = v___x_3541_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_a_3558_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3538_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3538_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
case 2:
{
lean_object* v_a_3566_; lean_object* v_a_3567_; 
v_a_3566_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3566_);
v_a_3567_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3567_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3339_ = v_a_3108_;
v_wi_3340_ = v_a_3566_;
v_d_3341_ = v_a_3567_;
v___y_3342_ = v_a_3110_;
goto v___jp_3338_;
}
case 3:
{
lean_object* v_a_3568_; lean_object* v_a_3569_; 
lean_dec_ref_known(v_a_3108_, 1);
v_a_3568_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3568_);
v_a_3569_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3569_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3383_ = v_a_3568_;
v_d_3384_ = v_a_3569_;
v___y_3385_ = v_a_3110_;
goto v___jp_3382_;
}
case 4:
{
lean_object* v_a_3570_; lean_object* v_a_3571_; 
lean_dec_ref(v_nCtx_3107_);
v_a_3570_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3570_);
v_a_3571_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3571_);
lean_dec_ref_known(v_a_3109_, 2);
v_nCtx_3107_ = v_a_3570_;
v_a_3109_ = v_a_3571_;
goto _start;
}
case 5:
{
lean_object* v_a_3573_; lean_object* v_a_3574_; 
v_a_3573_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_a_3573_);
v_a_3574_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3574_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3314_ = v_a_3108_;
v_n_3315_ = v_a_3573_;
v_d_3316_ = v_a_3574_;
v___y_3317_ = v_a_3110_;
goto v___jp_3313_;
}
case 6:
{
lean_object* v_a_3575_; 
v_a_3575_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3575_);
lean_dec_ref_known(v_a_3109_, 1);
v_ctx_3423_ = v_a_3108_;
v_d_3424_ = v_a_3575_;
v___y_3425_ = v_a_3110_;
goto v___jp_3422_;
}
case 7:
{
lean_object* v_a_3576_; lean_object* v_a_3577_; 
v_a_3576_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_a_3576_);
v_a_3577_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3577_);
lean_dec_ref_known(v_a_3109_, 2);
v_ctx_3389_ = v_a_3108_;
v_d_u2081_3390_ = v_a_3576_;
v_d_u2082_3391_ = v_a_3577_;
v___y_3392_ = v_a_3110_;
goto v___jp_3388_;
}
case 9:
{
lean_object* v_data_3578_; lean_object* v_msg_3579_; lean_object* v_children_3580_; 
v_data_3578_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_data_3578_);
v_msg_3579_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_msg_3579_);
v_children_3580_ = lean_ctor_get(v_a_3109_, 2);
lean_inc_ref(v_children_3580_);
lean_dec_ref_known(v_a_3109_, 3);
v_ctx_3247_ = v_a_3108_;
v_data_3248_ = v_data_3578_;
v_header_3249_ = v_msg_3579_;
v_children_3250_ = v_children_3580_;
v___y_3251_ = v_a_3110_;
goto v___jp_3246_;
}
case 10:
{
lean_object* v_val_3581_; lean_object* v_f_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_val_3581_ = lean_ctor_get(v_a_3108_, 0);
v_f_3582_ = lean_ctor_get(v_a_3109_, 0);
lean_inc_ref(v_f_3582_);
lean_dec_ref_known(v_a_3109_, 2);
v___x_3583_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_3107_, v_val_3581_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
v___y_3448_ = v_f_3582_;
v___y_3449_ = v_a_3110_;
v___y_3450_ = v_a_3108_;
v___y_3451_ = v___x_3584_;
goto v___jp_3447_;
}
default: 
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v_a_3109_, 1);
lean_inc_ref(v_a_3585_);
lean_dec_ref(v_a_3109_);
v_a_3109_ = v_a_3585_;
goto _start;
}
}
}
v___jp_3112_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3118_, 0, v___y_3115_);
lean_ctor_set(v___x_3118_, 1, v___y_3114_);
lean_ctor_set(v___x_3118_, 2, v_nodes_3116_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*3, v___y_3113_);
v___x_3119_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3118_, v___y_3117_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3138_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3138_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3138_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3137_; 
v_fst_3124_ = lean_ctor_get(v_a_3120_, 0);
v_snd_3125_ = lean_ctor_get(v_a_3120_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3120_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3127_ = v_a_3120_;
v_isShared_3128_ = v_isSharedCheck_3137_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_snd_3125_);
lean_inc(v_fst_3124_);
lean_dec(v_a_3120_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3137_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_fst_3124_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3130_);
v___x_3132_ = v___x_3127_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_snd_3125_);
v___x_3132_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3134_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3132_);
v___x_3134_ = v___x_3122_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_a_3139_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3119_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3119_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
v___jp_3147_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = lean_array_get_size(v___y_3152_);
v___x_3156_ = l_Array_toSubarray___redArg(v___y_3152_, v___x_3154_, v___x_3155_);
lean_inc(v___y_3150_);
v___x_3157_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v___y_3150_, v___y_3153_, v___x_3156_);
lean_dec(v___y_3153_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___y_3113_ = v___y_3148_;
v___y_3114_ = v___y_3149_;
v___y_3115_ = v___y_3150_;
v_nodes_3116_ = v___x_3158_;
v___y_3117_ = v___y_3151_;
goto v___jp_3112_;
}
v___jp_3159_:
{
lean_object* v___x_3165_; lean_object* v_defValue_3166_; 
v___x_3165_ = l_Lean_MessageData_maxTraceChildren;
v_defValue_3166_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_defValue_3166_);
v___y_3148_ = v___y_3160_;
v___y_3149_ = v___y_3162_;
v___y_3150_ = v___y_3161_;
v___y_3151_ = v___y_3164_;
v___y_3152_ = v___y_3163_;
v___y_3153_ = v_defValue_3166_;
goto v___jp_3147_;
}
v___jp_3167_:
{
size_t v_sz_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v_sz_3174_ = lean_array_size(v___y_3172_);
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v___y_3171_, v_nCtx_3107_, v_sz_3174_, v___x_3175_, v___y_3172_);
if (lean_obj_tag(v___y_3171_) == 0)
{
v___y_3160_ = v___y_3168_;
v___y_3161_ = v___y_3169_;
v___y_3162_ = v___y_3170_;
v___y_3163_ = v___x_3176_;
v___y_3164_ = v___y_3173_;
goto v___jp_3159_;
}
else
{
lean_object* v_val_3177_; lean_object* v_opts_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_val_3177_ = lean_ctor_get(v___y_3171_, 0);
lean_inc(v_val_3177_);
lean_dec_ref_known(v___y_3171_, 1);
v_opts_3178_ = lean_ctor_get(v_val_3177_, 3);
lean_inc_ref(v_opts_3178_);
lean_dec(v_val_3177_);
v___x_3179_ = l_Lean_MessageData_maxTraceChildren;
v___x_3180_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3178_, v___x_3179_);
lean_dec_ref(v_opts_3178_);
if (lean_obj_tag(v___x_3180_) == 0)
{
v___y_3160_ = v___y_3168_;
v___y_3161_ = v___y_3169_;
v___y_3162_ = v___y_3170_;
v___y_3163_ = v___x_3176_;
v___y_3164_ = v___y_3173_;
goto v___jp_3159_;
}
else
{
lean_object* v_val_3181_; 
v_val_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___y_3148_ = v___y_3168_;
v___y_3149_ = v___y_3170_;
v___y_3150_ = v___y_3169_;
v___y_3151_ = v___y_3173_;
v___y_3152_ = v___x_3176_;
v___y_3153_ = v_val_3181_;
goto v___jp_3147_;
}
}
}
v___jp_3182_:
{
if (v___y_3189_ == 0)
{
size_t v_sz_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v_sz_3190_ = lean_array_size(v___y_3187_);
v___x_3191_ = ((size_t)0ULL);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3107_, v___y_3186_, v_sz_3190_, v___x_3191_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v_fst_3194_; lean_object* v_snd_3195_; lean_object* v___x_3196_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v_fst_3194_ = lean_ctor_get(v_a_3193_, 0);
lean_inc(v_fst_3194_);
v_snd_3195_ = lean_ctor_get(v_a_3193_, 1);
lean_inc(v_snd_3195_);
lean_dec(v_a_3193_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_fst_3194_);
v___y_3113_ = v___y_3183_;
v___y_3114_ = v___y_3185_;
v___y_3115_ = v___y_3184_;
v_nodes_3116_ = v___x_3196_;
v___y_3117_ = v_snd_3195_;
goto v___jp_3112_;
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
v_a_3197_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3192_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3192_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
v___y_3168_ = v___y_3183_;
v___y_3169_ = v___y_3184_;
v___y_3170_ = v___y_3185_;
v___y_3171_ = v___y_3186_;
v___y_3172_ = v___y_3187_;
v___y_3173_ = v___y_3188_;
goto v___jp_3167_;
}
}
v___jp_3205_:
{
if (v___y_3206_ == 0)
{
v___y_3183_ = v___y_3206_;
v___y_3184_ = v___y_3208_;
v___y_3185_ = v_header_3211_;
v___y_3186_ = v___y_3209_;
v___y_3187_ = v___y_3210_;
v___y_3188_ = v___y_3212_;
v___y_3189_ = v___y_3207_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3213_ = lean_array_get_size(v___y_3210_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_nat_dec_eq(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
v___y_3168_ = v___y_3206_;
v___y_3169_ = v___y_3208_;
v___y_3170_ = v_header_3211_;
v___y_3171_ = v___y_3209_;
v___y_3172_ = v___y_3210_;
v___y_3173_ = v___y_3212_;
goto v___jp_3167_;
}
else
{
v___y_3183_ = v___y_3206_;
v___y_3184_ = v___y_3208_;
v___y_3185_ = v_header_3211_;
v___y_3186_ = v___y_3209_;
v___y_3187_ = v___y_3210_;
v___y_3188_ = v___y_3212_;
v___y_3189_ = v___y_3207_;
goto v___jp_3182_;
}
}
}
v___jp_3216_:
{
lean_object* v___x_3226_; double v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3226_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1));
v___x_3227_ = lean_float_sub(v___y_3218_, v___y_3225_);
v___x_3228_ = lean_float_to_string(v___x_3227_);
v___x_3229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3226_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3));
v___x_3232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v___y_3224_);
v___y_3206_ = v___y_3217_;
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3219_;
v___y_3209_ = v___y_3222_;
v___y_3210_ = v___y_3223_;
v_header_3211_ = v___x_3233_;
v___y_3212_ = v___y_3221_;
goto v___jp_3205_;
}
v___jp_3234_:
{
double v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3245_ = lean_float_beq(v___y_3241_, v___x_3244_);
if (v___x_3245_ == 0)
{
v___y_3217_ = v___y_3235_;
v___y_3218_ = v___y_3236_;
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3237_;
v___y_3221_ = v___y_3239_;
v___y_3222_ = v___y_3240_;
v___y_3223_ = v___y_3242_;
v___y_3224_ = v___y_3243_;
v___y_3225_ = v___y_3241_;
goto v___jp_3216_;
}
else
{
if (v___y_3237_ == 0)
{
v___y_3206_ = v___y_3235_;
v___y_3207_ = v___y_3237_;
v___y_3208_ = v___y_3238_;
v___y_3209_ = v___y_3240_;
v___y_3210_ = v___y_3242_;
v_header_3211_ = v___y_3243_;
v___y_3212_ = v___y_3239_;
goto v___jp_3205_;
}
else
{
v___y_3217_ = v___y_3235_;
v___y_3218_ = v___y_3236_;
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3237_;
v___y_3221_ = v___y_3239_;
v___y_3222_ = v___y_3240_;
v___y_3223_ = v___y_3242_;
v___y_3224_ = v___y_3243_;
v___y_3225_ = v___y_3241_;
goto v___jp_3216_;
}
}
}
v___jp_3246_:
{
lean_object* v_cls_3252_; lean_object* v_result_x3f_3253_; double v_startTime_3254_; double v_stopTime_3255_; uint8_t v_collapsed_3256_; uint8_t v___x_3257_; 
v_cls_3252_ = lean_ctor_get(v_data_3248_, 0);
lean_inc(v_cls_3252_);
v_result_x3f_3253_ = lean_ctor_get(v_data_3248_, 1);
lean_inc(v_result_x3f_3253_);
v_startTime_3254_ = lean_ctor_get_float(v_data_3248_, sizeof(void*)*3);
v_stopTime_3255_ = lean_ctor_get_float(v_data_3248_, sizeof(void*)*3 + 8);
v_collapsed_3256_ = lean_ctor_get_uint8(v_data_3248_, sizeof(void*)*3 + 16);
lean_dec_ref(v_data_3248_);
v___x_3257_ = l_Lean_Name_isAnonymous(v_cls_3252_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
lean_inc(v_ctx_3247_);
lean_inc_ref(v_nCtx_3107_);
v___x_3258_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3247_, v_header_3249_, v___y_3251_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v_fst_3260_; lean_object* v_snd_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3282_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v_fst_3260_ = lean_ctor_get(v_a_3259_, 0);
v_snd_3261_ = lean_ctor_get(v_a_3259_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3263_ = v_a_3259_;
v_isShared_3264_ = v_isSharedCheck_3282_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_snd_3261_);
lean_inc(v_fst_3260_);
lean_dec(v_a_3259_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3282_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4);
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 4);
lean_ctor_set(v___x_3263_, 1, v_fst_3260_);
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_fst_3260_);
v___x_3267_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
if (lean_obj_tag(v_result_x3f_3253_) == 0)
{
v___y_3235_ = v_collapsed_3256_;
v___y_3236_ = v_stopTime_3255_;
v___y_3237_ = v___x_3257_;
v___y_3238_ = v_cls_3252_;
v___y_3239_ = v_snd_3261_;
v___y_3240_ = v_ctx_3247_;
v___y_3241_ = v_startTime_3254_;
v___y_3242_ = v_children_3250_;
v___y_3243_ = v___x_3267_;
goto v___jp_3234_;
}
else
{
lean_object* v_val_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3280_; 
v_val_3268_ = lean_ctor_get(v_result_x3f_3253_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_result_x3f_3253_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3270_ = v_result_x3f_3253_;
v_isShared_3271_ = v_isSharedCheck_3280_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_val_3268_);
lean_dec(v_result_x3f_3253_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3280_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3272_ = lean_unbox(v_val_3268_);
lean_dec(v_val_3268_);
v___x_3273_ = l_Lean_TraceResult_toEmoji(v___x_3272_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 3);
lean_ctor_set(v___x_3270_, 0, v___x_3273_);
v___x_3275_ = v___x_3270_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6));
v___x_3277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
lean_ctor_set(v___x_3278_, 1, v___x_3267_);
v___y_3235_ = v_collapsed_3256_;
v___y_3236_ = v_stopTime_3255_;
v___y_3237_ = v___x_3257_;
v___y_3238_ = v_cls_3252_;
v___y_3239_ = v_snd_3261_;
v___y_3240_ = v_ctx_3247_;
v___y_3241_ = v_startTime_3254_;
v___y_3242_ = v_children_3250_;
v___y_3243_ = v___x_3278_;
goto v___jp_3234_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_3253_);
lean_dec(v_cls_3252_);
lean_dec_ref(v_children_3250_);
lean_dec(v_ctx_3247_);
lean_dec_ref(v_nCtx_3107_);
return v___x_3258_;
}
}
else
{
size_t v_sz_3283_; size_t v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_result_x3f_3253_);
lean_dec(v_cls_3252_);
lean_dec_ref(v_header_3249_);
v_sz_3283_ = lean_array_size(v_children_3250_);
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3107_, v_ctx_3247_, v_sz_3283_, v___x_3284_, v_children_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3304_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3304_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3304_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3303_; 
v_fst_3290_ = lean_ctor_get(v_a_3286_, 0);
v_snd_3291_ = lean_ctor_get(v_a_3286_, 1);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_a_3286_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3293_ = v_a_3286_;
v_isShared_3294_ = v_isSharedCheck_3303_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_snd_3291_);
lean_inc(v_fst_3290_);
lean_dec(v_a_3286_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3303_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3295_ = lean_array_to_list(v_fst_3290_);
v___x_3296_ = l_Std_Format_join(v___x_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3296_);
v___x_3298_ = v___x_3293_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_snd_3291_);
v___x_3298_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3298_);
v___x_3300_ = v___x_3288_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3285_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3285_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
v___jp_3313_:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3314_, v_d_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3337_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3337_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3337_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_fst_3323_; lean_object* v_snd_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3336_; 
v_fst_3323_ = lean_ctor_get(v_a_3319_, 0);
v_snd_3324_ = lean_ctor_get(v_a_3319_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_a_3319_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3326_ = v_a_3319_;
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_snd_3324_);
lean_inc(v_fst_3323_);
lean_dec(v_a_3319_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3336_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3328_ = lean_nat_to_int(v_n_3315_);
v___x_3329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_fst_3323_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3329_);
v___x_3331_ = v___x_3326_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_snd_3324_);
v___x_3331_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3333_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3331_);
v___x_3333_ = v___x_3321_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
else
{
lean_dec(v_n_3315_);
return v___x_3318_;
}
}
v___jp_3338_:
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3339_, v_d_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v_fst_3345_; lean_object* v_snd_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3381_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v_fst_3345_ = lean_ctor_get(v_a_3344_, 0);
v_snd_3346_ = lean_ctor_get(v_a_3344_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3344_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3348_ = v_a_3344_;
v_isShared_3349_ = v_isSharedCheck_3381_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_snd_3346_);
lean_inc(v_fst_3345_);
lean_dec(v_a_3344_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3381_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 2);
lean_ctor_set(v___x_3348_, 1, v_fst_3345_);
lean_ctor_set(v___x_3348_, 0, v_wi_3340_);
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_wi_3340_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_fst_3345_);
v___x_3351_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; 
v___x_3352_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3351_, v_snd_3346_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3371_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3371_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3371_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3370_; 
v_fst_3357_ = lean_ctor_get(v_a_3353_, 0);
v_snd_3358_ = lean_ctor_get(v_a_3353_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3360_ = v_a_3353_;
v_isShared_3361_ = v_isSharedCheck_3370_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_a_3353_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3370_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_fst_3357_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3363_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_snd_3358_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3365_);
v___x_3367_ = v___x_3355_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
v_a_3372_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3352_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3352_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_wi_3340_);
return v___x_3343_;
}
}
v___jp_3382_:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_ctx_3383_);
v_a_3108_ = v___x_3386_;
v_a_3109_ = v_d_3384_;
v_a_3110_ = v___y_3385_;
goto _start;
}
v___jp_3388_:
{
lean_object* v___x_3393_; 
lean_inc(v_ctx_3389_);
lean_inc_ref(v_nCtx_3107_);
v___x_3393_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3389_, v_d_u2081_3390_, v___y_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v_fst_3395_; lean_object* v_snd_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3421_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v_fst_3395_ = lean_ctor_get(v_a_3394_, 0);
v_snd_3396_ = lean_ctor_get(v_a_3394_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_a_3394_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3398_ = v_a_3394_;
v_isShared_3399_ = v_isSharedCheck_3421_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_snd_3396_);
lean_inc(v_fst_3395_);
lean_dec(v_a_3394_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3421_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3389_, v_d_u2082_3391_, v_snd_3396_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3420_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_fst_3405_; lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3419_; 
v_fst_3405_ = lean_ctor_get(v_a_3401_, 0);
v_snd_3406_ = lean_ctor_get(v_a_3401_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_a_3401_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3408_ = v_a_3401_;
v_isShared_3409_ = v_isSharedCheck_3419_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_inc(v_fst_3405_);
lean_dec(v_a_3401_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3419_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 5);
lean_ctor_set(v___x_3398_, 1, v_fst_3405_);
v___x_3411_ = v___x_3398_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_fst_3395_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_fst_3405_);
v___x_3411_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3411_);
v___x_3413_ = v___x_3408_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_snd_3406_);
v___x_3413_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3413_);
v___x_3415_ = v___x_3403_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3398_);
lean_dec(v_fst_3395_);
return v___x_3400_;
}
}
}
else
{
lean_dec_ref(v_d_u2082_3391_);
lean_dec(v_ctx_3389_);
lean_dec_ref(v_nCtx_3107_);
return v___x_3393_;
}
}
v___jp_3422_:
{
lean_object* v___x_3426_; 
v___x_3426_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3107_, v_ctx_3423_, v_d_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3445_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3445_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3445_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3444_; 
v_fst_3431_ = lean_ctor_get(v_a_3427_, 0);
v_snd_3432_ = lean_ctor_get(v_a_3427_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3427_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3434_ = v_a_3427_;
v_isShared_3435_ = v_isSharedCheck_3444_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_a_3427_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3444_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3436_ = 0;
v___x_3437_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3437_, 0, v_fst_3431_);
lean_ctor_set_uint8(v___x_3437_, sizeof(void*)*1, v___x_3436_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3437_);
v___x_3439_ = v___x_3434_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_snd_3432_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3439_);
v___x_3441_ = v___x_3429_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
else
{
return v___x_3426_;
}
}
v___jp_3447_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = lean_apply_2(v___y_3448_, v___y_3451_, lean_box(0));
v___x_3453_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_3452_, v___x_3446_);
lean_dec(v___x_3452_);
if (lean_obj_tag(v___x_3453_) == 1)
{
lean_object* v_val_3454_; 
v_val_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v_a_3108_ = v___y_3450_;
v_a_3109_ = v_val_3454_;
v_a_3110_ = v___y_3449_;
goto _start;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v___x_3453_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_nCtx_3107_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object* v_nCtx_3587_, lean_object* v_ctx_3588_, size_t v_sz_3589_, size_t v_i_3590_, lean_object* v_bs_3591_, lean_object* v___y_3592_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3590_, v_sz_3589_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
lean_dec(v_ctx_3588_);
lean_dec_ref(v_nCtx_3587_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v_bs_3591_);
lean_ctor_set(v___x_3595_, 1, v___y_3592_);
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
else
{
lean_object* v_v_3597_; lean_object* v___x_3598_; lean_object* v_bs_x27_3599_; lean_object* v___x_3600_; 
v_v_3597_ = lean_array_uget(v_bs_3591_, v_i_3590_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v_bs_x27_3599_ = lean_array_uset(v_bs_3591_, v_i_3590_, v___x_3598_);
lean_inc(v_ctx_3588_);
lean_inc_ref(v_nCtx_3587_);
v___x_3600_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3587_, v_ctx_3588_, v_v_3597_, v___y_3592_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_fst_3602_; lean_object* v_snd_3603_; size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v_fst_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_fst_3602_);
v_snd_3603_ = lean_ctor_get(v_a_3601_, 1);
lean_inc(v_snd_3603_);
lean_dec(v_a_3601_);
v___x_3604_ = ((size_t)1ULL);
v___x_3605_ = lean_usize_add(v_i_3590_, v___x_3604_);
v___x_3606_ = lean_array_uset(v_bs_x27_3599_, v_i_3590_, v_fst_3602_);
v_i_3590_ = v___x_3605_;
v_bs_3591_ = v___x_3606_;
v___y_3592_ = v_snd_3603_;
goto _start;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v_bs_x27_3599_);
lean_dec(v_ctx_3588_);
lean_dec_ref(v_nCtx_3587_);
v_a_3608_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3600_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3600_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3___boxed(lean_object* v_nCtx_3616_, lean_object* v_ctx_3617_, lean_object* v_sz_3618_, lean_object* v_i_3619_, lean_object* v_bs_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
size_t v_sz_boxed_3623_; size_t v_i_boxed_3624_; lean_object* v_res_3625_; 
v_sz_boxed_3623_ = lean_unbox_usize(v_sz_3618_);
lean_dec(v_sz_3618_);
v_i_boxed_3624_ = lean_unbox_usize(v_i_3619_);
lean_dec(v_i_3619_);
v_res_3625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(v_nCtx_3616_, v_ctx_3617_, v_sz_boxed_3623_, v_i_boxed_3624_, v_bs_3620_, v___y_3621_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object* v_nCtx_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object* v_msgData_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0));
v___x_3640_ = lean_box(0);
v___x_3641_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1));
v___x_3642_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v___x_3639_, v___x_3640_, v_msgData_3637_, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object* v_msgData_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3643_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object* v_g_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_Widget_goalToInteractive(v_g_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3663_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_a_3653_);
v___x_3658_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
v___x_3659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3659_);
v___x_3661_ = v___x_3655_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_a_3664_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3652_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3652_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object* v_g_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(v_g_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object* v_f_3679_, size_t v_sz_3680_, size_t v_i_3681_, lean_object* v_bs_3682_){
_start:
{
uint8_t v___x_3684_; 
v___x_3684_ = lean_usize_dec_lt(v_i_3681_, v_sz_3680_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec_ref(v_f_3679_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_bs_3682_);
return v___x_3685_;
}
else
{
lean_object* v_v_3686_; lean_object* v___x_3687_; lean_object* v_bs_x27_3688_; lean_object* v___x_3689_; 
v_v_3686_ = lean_array_uget(v_bs_3682_, v_i_3681_);
v___x_3687_ = lean_unsigned_to_nat(0u);
v_bs_x27_3688_ = lean_array_uset(v_bs_3682_, v_i_3681_, v___x_3687_);
lean_inc_ref(v_f_3679_);
v___x_3689_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3679_, v_v_3686_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; size_t v___x_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3689_, 1);
v___x_3691_ = ((size_t)1ULL);
v___x_3692_ = lean_usize_add(v_i_3681_, v___x_3691_);
v___x_3693_ = lean_array_uset(v_bs_x27_3688_, v_i_3681_, v_a_3690_);
v_i_3681_ = v___x_3692_;
v_bs_3682_ = v___x_3693_;
goto _start;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v_bs_x27_3688_);
lean_dec_ref(v_f_3679_);
v_a_3695_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3689_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3689_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object* v_f_3703_, lean_object* v_x_3704_){
_start:
{
switch(lean_obj_tag(v_x_3704_))
{
case 0:
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v_f_3703_);
v_a_3706_ = lean_ctor_get(v_x_3704_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_x_3704_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3708_ = v_x_3704_;
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v_x_3704_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
}
case 1:
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3741_; 
v_a_3715_ = lean_ctor_get(v_x_3704_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_x_3704_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3717_ = v_x_3704_;
v_isShared_3718_ = v_isSharedCheck_3741_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v_x_3704_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3741_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
size_t v_sz_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v_sz_3719_ = lean_array_size(v_a_3715_);
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3703_, v_sz_3719_, v___x_3720_, v_a_3715_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3732_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_a_3722_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3717_);
v_a_3733_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3721_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3721_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
default: 
{
lean_object* v_a_3742_; lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3742_ = lean_ctor_get(v_x_3704_, 0);
lean_inc(v_a_3742_);
v_a_3743_ = lean_ctor_get(v_x_3704_, 1);
lean_inc_ref(v_a_3743_);
lean_dec_ref_known(v_x_3704_, 2);
v___x_3744_ = lean_apply_3(v_f_3703_, v_a_3742_, v_a_3743_, lean_box(0));
return v___x_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg___boxed(lean_object* v_f_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3745_, v_x_3746_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object* v_f_3749_, lean_object* v_sz_3750_, lean_object* v_i_3751_, lean_object* v_bs_3752_, lean_object* v___y_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3750_);
lean_dec(v_sz_3750_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3749_, v_sz_boxed_3754_, v_i_boxed_3755_, v_bs_3752_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t v_sz_3757_, size_t v_i_3758_, lean_object* v_bs_3759_){
_start:
{
uint8_t v___x_3761_; 
v___x_3761_ = lean_usize_dec_lt(v_i_3758_, v_sz_3757_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3762_, 0, v_bs_3759_);
return v___x_3762_;
}
else
{
lean_object* v_v_3763_; lean_object* v___x_3764_; lean_object* v_bs_x27_3765_; lean_object* v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v_v_3763_ = lean_array_uget(v_bs_3759_, v_i_3758_);
v___x_3764_ = lean_unsigned_to_nat(0u);
v_bs_x27_3765_ = lean_array_uset(v_bs_3759_, v_i_3758_, v___x_3764_);
v___x_3766_ = l_Lean_Server_WithRpcRef_mk___redArg(v_v_3763_);
v___x_3767_ = ((size_t)1ULL);
v___x_3768_ = lean_usize_add(v_i_3758_, v___x_3767_);
v___x_3769_ = lean_array_uset(v_bs_x27_3765_, v_i_3758_, v___x_3766_);
v_i_3758_ = v___x_3768_;
v_bs_3759_ = v___x_3769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object* v_sz_3771_, lean_object* v_i_3772_, lean_object* v_bs_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3771_);
lean_dec(v_sz_3771_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3772_);
lean_dec(v_i_3772_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_boxed_3775_, v_i_boxed_3776_, v_bs_3773_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object* v_col_3778_, lean_object* v_embeds_3779_, size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_bs_3782_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v_embeds_3779_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_bs_3782_);
return v___x_3785_;
}
else
{
lean_object* v_v_3786_; lean_object* v___x_3787_; lean_object* v_bs_x27_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_v_3786_ = lean_array_uget(v_bs_3782_, v_i_3781_);
v___x_3787_ = lean_unsigned_to_nat(0u);
v_bs_x27_3788_ = lean_array_uset(v_bs_3782_, v_i_3781_, v___x_3787_);
v___x_3789_ = lean_unsigned_to_nat(2u);
v___x_3790_ = lean_nat_add(v_col_3778_, v___x_3789_);
lean_inc_ref(v_embeds_3779_);
v___x_3791_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3779_, v_v_3786_, v___x_3790_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = ((size_t)1ULL);
v___x_3794_ = lean_usize_add(v_i_3781_, v___x_3793_);
v___x_3795_ = lean_array_uset(v_bs_x27_3788_, v_i_3781_, v_a_3792_);
v_i_3781_ = v___x_3794_;
v_bs_3782_ = v___x_3795_;
goto _start;
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_bs_x27_3788_);
lean_dec_ref(v_embeds_3779_);
v_a_3797_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3791_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3791_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object* v___x_3805_, lean_object* v_embeds_3806_, lean_object* v_indent_3807_, lean_object* v_x_3808_, lean_object* v_tt_3809_){
_start:
{
lean_object* v_fst_3811_; lean_object* v_snd_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3925_; 
v_fst_3811_ = lean_ctor_get(v_x_3808_, 0);
v_snd_3812_ = lean_ctor_get(v_x_3808_, 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_x_3808_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3814_ = v_x_3808_;
v_isShared_3815_ = v_isSharedCheck_3925_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_snd_3812_);
lean_inc(v_fst_3811_);
lean_dec(v_x_3808_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3925_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_array_get(v___x_3805_, v_embeds_3806_, v_fst_3811_);
lean_dec(v_fst_3811_);
switch(lean_obj_tag(v___x_3816_))
{
case 0:
{
lean_object* v_ctx_3817_; lean_object* v_infos_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3829_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3812_);
lean_dec(v_indent_3807_);
lean_dec_ref(v_embeds_3806_);
v_ctx_3817_ = lean_ctor_get(v___x_3816_, 0);
v_infos_3818_ = lean_ctor_get(v___x_3816_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3820_ = v___x_3816_;
v_isShared_3821_ = v_isSharedCheck_3829_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_infos_3818_);
lean_inc(v_ctx_3817_);
lean_dec(v___x_3816_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3829_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3822_ = l_Lean_Widget_tagCodeInfos(v_ctx_3817_, v_infos_3818_, v_tt_3809_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
v___x_3824_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 2);
lean_ctor_set(v___x_3820_, 1, v___x_3824_);
lean_ctor_set(v___x_3820_, 0, v___x_3823_);
v___x_3826_ = v___x_3820_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
}
}
case 1:
{
lean_object* v_ctx_3830_; lean_object* v_lctx_3831_; lean_object* v_g_3832_; lean_object* v___f_3833_; lean_object* v___x_3834_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3812_);
lean_dec_ref(v_tt_3809_);
lean_dec(v_indent_3807_);
lean_dec_ref(v_embeds_3806_);
v_ctx_3830_ = lean_ctor_get(v___x_3816_, 0);
lean_inc_ref(v_ctx_3830_);
v_lctx_3831_ = lean_ctor_get(v___x_3816_, 1);
lean_inc_ref(v_lctx_3831_);
v_g_3832_ = lean_ctor_get(v___x_3816_, 2);
lean_inc(v_g_3832_);
lean_dec_ref_known(v___x_3816_, 3);
v___f_3833_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3833_, 0, v_g_3832_);
v___x_3834_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_3830_, v_lctx_3831_, v___f_3833_);
return v___x_3834_;
}
case 2:
{
lean_object* v_wi_3835_; lean_object* v_alt_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_tt_3809_);
lean_dec(v_indent_3807_);
v_wi_3835_ = lean_ctor_get(v___x_3816_, 0);
v_alt_3836_ = lean_ctor_get(v___x_3816_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3838_ = v___x_3816_;
v_isShared_3839_ = v_isSharedCheck_3856_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_alt_3836_);
lean_inc(v_wi_3835_);
lean_dec(v___x_3816_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3856_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3806_, v_alt_3836_, v_snd_3812_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3855_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3855_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3855_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 1, v_a_3841_);
v___x_3846_ = v___x_3838_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_wi_3835_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 2);
lean_ctor_set(v___x_3814_, 1, v___x_3847_);
lean_ctor_set(v___x_3814_, 0, v___x_3846_);
v___x_3849_ = v___x_3814_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3849_);
v___x_3851_ = v___x_3843_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
else
{
lean_del_object(v___x_3838_);
lean_dec_ref(v_wi_3835_);
lean_del_object(v___x_3814_);
return v___x_3840_;
}
}
}
case 3:
{
lean_object* v_cls_3857_; lean_object* v_msg_3858_; uint8_t v_collapsed_3859_; lean_object* v_children_3860_; lean_object* v_col_3861_; lean_object* v_children_3863_; 
lean_dec_ref(v_tt_3809_);
v_cls_3857_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_cls_3857_);
v_msg_3858_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_msg_3858_);
v_collapsed_3859_ = lean_ctor_get_uint8(v___x_3816_, sizeof(void*)*3);
v_children_3860_ = lean_ctor_get(v___x_3816_, 2);
lean_inc_ref(v_children_3860_);
lean_dec_ref_known(v___x_3816_, 3);
v_col_3861_ = lean_nat_add(v_indent_3807_, v_snd_3812_);
lean_dec(v_snd_3812_);
if (lean_obj_tag(v_children_3860_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3897_; 
v_a_3878_ = lean_ctor_get(v_children_3860_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_children_3860_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3880_ = v_children_3860_;
v_isShared_3881_ = v_isSharedCheck_3897_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v_children_3860_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3897_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
size_t v_sz_3882_; size_t v___x_3883_; lean_object* v___x_3884_; 
v_sz_3882_ = lean_array_size(v_a_3878_);
v___x_3883_ = ((size_t)0ULL);
lean_inc_ref(v_embeds_3806_);
v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3861_, v_embeds_3806_, v_sz_3882_, v___x_3883_, v_a_3878_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v_a_3885_);
v___x_3887_ = v___x_3880_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
v_children_3863_ = v___x_3887_;
goto v___jp_3862_;
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_del_object(v___x_3880_);
lean_dec(v_col_3861_);
lean_dec(v_msg_3858_);
lean_dec(v_cls_3857_);
lean_del_object(v___x_3814_);
lean_dec(v_indent_3807_);
lean_dec_ref(v_embeds_3806_);
v_a_3889_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3884_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3884_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3921_; 
v_a_3898_ = lean_ctor_get(v_children_3860_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_children_3860_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3900_ = v_children_3860_;
v_isShared_3901_ = v_isSharedCheck_3921_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v_children_3860_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3921_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
size_t v_sz_3902_; size_t v___x_3903_; lean_object* v___x_3904_; 
v_sz_3902_ = lean_array_size(v_a_3898_);
v___x_3903_ = ((size_t)0ULL);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_3902_, v___x_3903_, v_a_3898_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = lean_unsigned_to_nat(2u);
v___x_3907_ = lean_nat_add(v_col_3861_, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_a_3905_);
v___x_3909_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_3908_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3909_);
v___x_3911_ = v___x_3900_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
v_children_3863_ = v___x_3911_;
goto v___jp_3862_;
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_del_object(v___x_3900_);
lean_dec(v_col_3861_);
lean_dec(v_msg_3858_);
lean_dec(v_cls_3857_);
lean_del_object(v___x_3814_);
lean_dec(v_indent_3807_);
lean_dec_ref(v_embeds_3806_);
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3904_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3904_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
v___jp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3806_, v_msg_3858_, v_col_3861_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3877_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3877_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3877_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3869_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_3869_, 0, v_indent_3807_);
lean_ctor_set(v___x_3869_, 1, v_cls_3857_);
lean_ctor_set(v___x_3869_, 2, v_a_3865_);
lean_ctor_set(v___x_3869_, 3, v_children_3863_);
lean_ctor_set_uint8(v___x_3869_, sizeof(void*)*4, v_collapsed_3859_);
v___x_3870_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 2);
lean_ctor_set(v___x_3814_, 1, v___x_3870_);
lean_ctor_set(v___x_3814_, 0, v___x_3869_);
v___x_3872_ = v___x_3814_;
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
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3872_);
v___x_3874_ = v___x_3867_;
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
else
{
lean_dec_ref(v_children_3863_);
lean_dec(v_cls_3857_);
lean_del_object(v___x_3814_);
lean_dec(v_indent_3807_);
return v___x_3864_;
}
}
}
default: 
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3812_);
lean_dec(v_indent_3807_);
lean_dec_ref(v_embeds_3806_);
v___x_3922_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3809_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed(lean_object* v___x_3926_, lean_object* v_embeds_3927_, lean_object* v_indent_3928_, lean_object* v_x_3929_, lean_object* v_tt_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(v___x_3926_, v_embeds_3927_, v_indent_3928_, v_x_3929_, v_tt_3930_);
lean_dec(v___x_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(lean_object* v_embeds_3933_, lean_object* v_fmt_3934_, lean_object* v_indent_3935_){
_start:
{
lean_object* v___x_3937_; lean_object* v___f_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3937_ = l_Lean_Widget_instInhabitedEmbedFmt_default;
lean_inc(v_indent_3935_);
v___f_3938_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3938_, 0, v___x_3937_);
lean_closure_set(v___f_3938_, 1, v_embeds_3933_);
lean_closure_set(v___f_3938_, 2, v_indent_3935_);
v___x_3939_ = l_Std_Format_defWidth;
v___x_3940_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_3934_, v_indent_3935_, v___x_3939_);
v___x_3941_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v___f_3938_, v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___boxed(lean_object* v_embeds_3942_, lean_object* v_fmt_3943_, lean_object* v_indent_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3942_, v_fmt_3943_, v_indent_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object* v_col_3947_, lean_object* v_embeds_3948_, lean_object* v_sz_3949_, lean_object* v_i_3950_, lean_object* v_bs_3951_, lean_object* v___y_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3949_);
lean_dec(v_sz_3949_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3950_);
lean_dec(v_i_3950_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3947_, v_embeds_3948_, v_sz_boxed_3953_, v_i_boxed_3954_, v_bs_3951_);
lean_dec(v_col_3947_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object* v_00_u03b1_3956_, lean_object* v_00_u03b2_3957_, lean_object* v_f_3958_, lean_object* v_x_3959_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3958_, v_x_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___boxed(lean_object* v_00_u03b1_3962_, lean_object* v_00_u03b2_3963_, lean_object* v_f_3964_, lean_object* v_x_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(v_00_u03b1_3962_, v_00_u03b2_3963_, v_f_3964_, v_x_3965_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object* v_00_u03b1_3968_, lean_object* v_00_u03b2_3969_, lean_object* v_f_3970_, size_t v_sz_3971_, size_t v_i_3972_, lean_object* v_bs_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3970_, v_sz_3971_, v_i_3972_, v_bs_3973_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3976_, lean_object* v_00_u03b2_3977_, lean_object* v_f_3978_, lean_object* v_sz_3979_, lean_object* v_i_3980_, lean_object* v_bs_3981_, lean_object* v___y_3982_){
_start:
{
size_t v_sz_boxed_3983_; size_t v_i_boxed_3984_; lean_object* v_res_3985_; 
v_sz_boxed_3983_ = lean_unbox_usize(v_sz_3979_);
lean_dec(v_sz_3979_);
v_i_boxed_3984_ = lean_unbox_usize(v_i_3980_);
lean_dec(v_i_3980_);
v_res_3985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(v_00_u03b1_3976_, v_00_u03b2_3977_, v_f_3978_, v_sz_boxed_3983_, v_i_boxed_3984_, v_bs_3981_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object* v_x_3986_, lean_object* v_tt_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object* v_x_3990_, lean_object* v_tt_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_Widget_msgToInteractive___lam__0(v_x_3990_, v_tt_3991_);
lean_dec_ref(v_x_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object* v_msgData_3994_, uint8_t v_hasWidgets_3995_, lean_object* v_indent_3996_){
_start:
{
if (v_hasWidgets_3995_ == 0)
{
lean_object* v___f_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec(v_indent_3996_);
v___f_3998_ = ((lean_object*)(l_Lean_Widget_msgToInteractive___closed__0));
v___x_3999_ = lean_box(0);
v___x_4000_ = l_Lean_MessageData_format(v_msgData_3994_, v___x_3999_);
v___x_4001_ = lean_unsigned_to_nat(0u);
v___x_4002_ = l_Std_Format_defWidth;
v___x_4003_ = l_Lean_Widget_TaggedText_prettyTagged(v___x_4000_, v___x_4001_, v___x_4002_);
v___x_4004_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_3998_, v___x_4003_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; 
v___x_4006_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3994_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v_fst_4008_; lean_object* v_snd_4009_; lean_object* v___x_4010_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v_fst_4008_ = lean_ctor_get(v_a_4007_, 0);
lean_inc(v_fst_4008_);
v_snd_4009_ = lean_ctor_get(v_a_4007_, 1);
lean_inc(v_snd_4009_);
lean_dec(v_a_4007_);
v___x_4010_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_snd_4009_, v_fst_4008_, v_indent_3996_);
return v___x_4010_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_indent_3996_);
v_a_4011_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4006_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4006_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object* v_msgData_4019_, lean_object* v_hasWidgets_4020_, lean_object* v_indent_4021_, lean_object* v_a_4022_){
_start:
{
uint8_t v_hasWidgets_boxed_4023_; lean_object* v_res_4024_; 
v_hasWidgets_boxed_4023_ = lean_unbox(v_hasWidgets_4020_);
v_res_4024_ = l_Lean_Widget_msgToInteractive(v_msgData_4019_, v_hasWidgets_boxed_4023_, v_indent_4021_);
return v_res_4024_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object* v_x_4030_){
_start:
{
lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__2));
v___x_4032_ = lean_name_eq(v_x_4030_, v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object* v_x_4033_){
_start:
{
uint8_t v_res_4034_; lean_object* v_r_4035_; 
v_res_4034_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(v_x_4033_);
lean_dec(v_x_4033_);
v_r_4035_ = lean_box(v_res_4034_);
return v_r_4035_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object* v_x_4039_){
_start:
{
lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4040_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1));
v___x_4041_ = lean_name_eq(v_x_4039_, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object* v_x_4042_){
_start:
{
uint8_t v_res_4043_; lean_object* v_r_4044_; 
v_res_4043_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(v_x_4042_);
lean_dec(v_x_4042_);
v_r_4044_ = lean_box(v_res_4043_);
return v_r_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object* v_text_4083_, lean_object* v_m_4084_, uint8_t v_hasWidgets_4085_){
_start:
{
lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v_pos_4100_; lean_object* v_endPos_4101_; uint8_t v_keepFullRange_4102_; uint8_t v_severity_4103_; uint8_t v_isSilent_4104_; lean_object* v_data_4105_; uint8_t v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___f_4154_; lean_object* v___f_4155_; lean_object* v___y_4157_; lean_object* v___y_4158_; uint8_t v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; uint8_t v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v_low_4190_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4200_; 
v_pos_4100_ = lean_ctor_get(v_m_4084_, 1);
lean_inc_ref_n(v_pos_4100_, 2);
v_endPos_4101_ = lean_ctor_get(v_m_4084_, 2);
lean_inc(v_endPos_4101_);
v_keepFullRange_4102_ = lean_ctor_get_uint8(v_m_4084_, sizeof(void*)*5);
v_severity_4103_ = lean_ctor_get_uint8(v_m_4084_, sizeof(void*)*5 + 1);
v_isSilent_4104_ = lean_ctor_get_uint8(v_m_4084_, sizeof(void*)*5 + 2);
v_data_4105_ = lean_ctor_get(v_m_4084_, 4);
lean_inc(v_data_4105_);
lean_dec_ref(v_m_4084_);
v___f_4154_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__2));
v___f_4155_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__3));
lean_inc_ref(v_text_4083_);
v_low_4190_ = l_Lean_FileMap_leanPosToLspPos(v_text_4083_, v_pos_4100_);
if (lean_obj_tag(v_endPos_4101_) == 0)
{
lean_inc_ref(v_pos_4100_);
v___y_4200_ = v_pos_4100_;
goto v___jp_4199_;
}
else
{
lean_object* v_val_4222_; 
v_val_4222_ = lean_ctor_get(v_endPos_4101_, 0);
lean_inc(v_val_4222_);
v___y_4200_ = v_val_4222_;
goto v___jp_4199_;
}
v___jp_4087_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___y_4089_);
v___x_4098_ = lean_box(0);
lean_inc(v___y_4090_);
lean_inc(v___y_4094_);
lean_inc(v___y_4095_);
lean_inc(v___y_4091_);
v___x_4099_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4088_);
lean_ctor_set(v___x_4099_, 1, v___x_4097_);
lean_ctor_set(v___x_4099_, 2, v___y_4092_);
lean_ctor_set(v___x_4099_, 3, v___y_4091_);
lean_ctor_set(v___x_4099_, 4, v___y_4096_);
lean_ctor_set(v___x_4099_, 5, v___y_4095_);
lean_ctor_set(v___x_4099_, 6, v___y_4093_);
lean_ctor_set(v___x_4099_, 7, v___y_4094_);
lean_ctor_set(v___x_4099_, 8, v___y_4090_);
lean_ctor_set(v___x_4099_, 9, v___x_4098_);
lean_ctor_set(v___x_4099_, 10, v___x_4098_);
return v___x_4099_;
}
v___jp_4106_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = l_Lean_MessageData_kind(v_data_4105_);
lean_dec(v_data_4105_);
v___x_4117_ = l_Lean_errorNameOfKind_x3f(v___x_4116_);
lean_dec(v___x_4116_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_box(0);
v___y_4088_ = v___y_4109_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4110_;
v___y_4091_ = v___y_4112_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4115_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4114_;
v___y_4096_ = v___x_4118_;
goto v___jp_4087_;
}
else
{
lean_object* v_val_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4128_; 
v_val_4119_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4121_ = v___x_4117_;
v_isShared_4122_ = v_isSharedCheck_4128_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_val_4119_);
lean_dec(v___x_4117_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4128_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4123_ = l_Lean_Name_toString(v_val_4119_, v___y_4107_);
v___x_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4124_);
v___x_4126_ = v___x_4121_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
v___y_4088_ = v___y_4109_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4110_;
v___y_4091_ = v___y_4112_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4115_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4114_;
v___y_4096_ = v___x_4126_;
goto v___jp_4087_;
}
}
}
}
v___jp_4129_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_unsigned_to_nat(0u);
lean_inc(v_data_4105_);
v___x_4139_ = l_Lean_Widget_msgToInteractive(v_data_4105_, v_hasWidgets_4085_, v___x_4138_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___y_4107_ = v___y_4130_;
v___y_4108_ = v___y_4131_;
v___y_4109_ = v___y_4132_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___y_4134_;
v___y_4113_ = v___y_4135_;
v___y_4114_ = v___y_4136_;
v___y_4115_ = v_a_4140_;
goto v___jp_4106_;
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4153_; 
v_a_4141_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4143_ = v___x_4139_;
v_isShared_4144_ = v_isSharedCheck_4153_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4139_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4153_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4145_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__0));
v___x_4146_ = lean_io_error_to_string(v_a_4141_);
v___x_4147_ = lean_string_append(v___x_4145_, v___x_4146_);
lean_dec_ref(v___x_4146_);
v___x_4148_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__1));
v___x_4149_ = lean_string_append(v___x_4147_, v___x_4148_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4149_);
v___x_4151_ = v___x_4143_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
v___y_4107_ = v___y_4130_;
v___y_4108_ = v___y_4131_;
v___y_4109_ = v___y_4132_;
v___y_4110_ = v___y_4137_;
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___y_4134_;
v___y_4113_ = v___y_4135_;
v___y_4114_ = v___y_4136_;
v___y_4115_ = v___x_4151_;
goto v___jp_4106_;
}
}
}
}
v___jp_4156_:
{
uint8_t v___x_4164_; 
lean_inc(v_data_4105_);
v___x_4164_ = l_Lean_MessageData_hasTag(v___f_4154_, v_data_4105_);
if (v___x_4164_ == 0)
{
uint8_t v___x_4165_; 
lean_inc(v_data_4105_);
v___x_4165_ = l_Lean_MessageData_hasTag(v___f_4155_, v_data_4105_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_box(0);
v___y_4130_ = v___y_4159_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4157_;
v___y_4133_ = v___y_4161_;
v___y_4134_ = v___y_4160_;
v___y_4135_ = v___y_4163_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___x_4166_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__5));
v___y_4130_ = v___y_4159_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4157_;
v___y_4133_ = v___y_4161_;
v___y_4134_ = v___y_4160_;
v___y_4135_ = v___y_4163_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___x_4167_;
goto v___jp_4129_;
}
}
else
{
lean_object* v___x_4168_; 
v___x_4168_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__7));
v___y_4130_ = v___y_4159_;
v___y_4131_ = v___y_4158_;
v___y_4132_ = v___y_4157_;
v___y_4133_ = v___y_4161_;
v___y_4134_ = v___y_4160_;
v___y_4135_ = v___y_4163_;
v___y_4136_ = v___y_4162_;
v___y_4137_ = v___x_4168_;
goto v___jp_4129_;
}
}
v___jp_4169_:
{
lean_object* v_source_x3f_4175_; uint8_t v___x_4176_; 
v_source_x3f_4175_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__9));
lean_inc(v_data_4105_);
v___x_4176_ = l_Lean_MessageData_isDeprecationWarning(v_data_4105_);
if (v___x_4176_ == 0)
{
uint8_t v___x_4177_; 
lean_inc(v_data_4105_);
v___x_4177_ = l_Lean_MessageData_isUnusedVariableWarning(v_data_4105_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_box(0);
v___y_4157_ = v___y_4172_;
v___y_4158_ = v___y_4171_;
v___y_4159_ = v___y_4170_;
v___y_4160_ = v___y_4174_;
v___y_4161_ = v___y_4173_;
v___y_4162_ = v_source_x3f_4175_;
v___y_4163_ = v___x_4178_;
goto v___jp_4156_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__11));
v___y_4157_ = v___y_4172_;
v___y_4158_ = v___y_4171_;
v___y_4159_ = v___y_4170_;
v___y_4160_ = v___y_4174_;
v___y_4161_ = v___y_4173_;
v___y_4162_ = v_source_x3f_4175_;
v___y_4163_ = v___x_4179_;
goto v___jp_4156_;
}
}
else
{
lean_object* v___x_4180_; 
v___x_4180_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__13));
v___y_4157_ = v___y_4172_;
v___y_4158_ = v___y_4171_;
v___y_4159_ = v___y_4170_;
v___y_4160_ = v___y_4174_;
v___y_4161_ = v___y_4173_;
v___y_4162_ = v_source_x3f_4175_;
v___y_4163_ = v___x_4180_;
goto v___jp_4156_;
}
}
v___jp_4181_:
{
lean_object* v___x_4185_; lean_object* v_severity_x3f_4186_; uint8_t v___x_4187_; 
v___x_4185_ = lean_box(v___y_4184_);
v_severity_x3f_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_severity_x3f_4186_, 0, v___x_4185_);
v___x_4187_ = 1;
if (v_isSilent_4104_ == 0)
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_box(0);
v___y_4170_ = v___x_4187_;
v___y_4171_ = v___y_4183_;
v___y_4172_ = v___y_4182_;
v___y_4173_ = v_severity_x3f_4186_;
v___y_4174_ = v___x_4188_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4189_; 
v___x_4189_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__14));
v___y_4170_ = v___x_4187_;
v___y_4171_ = v___y_4183_;
v___y_4172_ = v___y_4182_;
v___y_4173_ = v_severity_x3f_4186_;
v___y_4174_ = v___x_4189_;
goto v___jp_4169_;
}
}
v___jp_4191_:
{
lean_object* v_range_4194_; lean_object* v_fullRange_4195_; 
lean_inc_ref(v_low_4190_);
v_range_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_4194_, 0, v_low_4190_);
lean_ctor_set(v_range_4194_, 1, v___y_4193_);
v_fullRange_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_fullRange_4195_, 0, v_low_4190_);
lean_ctor_set(v_fullRange_4195_, 1, v___y_4192_);
switch(v_severity_4103_)
{
case 0:
{
uint8_t v___x_4196_; 
v___x_4196_ = 2;
v___y_4182_ = v_range_4194_;
v___y_4183_ = v_fullRange_4195_;
v___y_4184_ = v___x_4196_;
goto v___jp_4181_;
}
case 1:
{
uint8_t v___x_4197_; 
v___x_4197_ = 1;
v___y_4182_ = v_range_4194_;
v___y_4183_ = v_fullRange_4195_;
v___y_4184_ = v___x_4197_;
goto v___jp_4181_;
}
default: 
{
uint8_t v___x_4198_; 
v___x_4198_ = 0;
v___y_4182_ = v_range_4194_;
v___y_4183_ = v_fullRange_4195_;
v___y_4184_ = v___x_4198_;
goto v___jp_4181_;
}
}
}
v___jp_4199_:
{
lean_object* v_fullHigh_4201_; 
lean_inc_ref(v_text_4083_);
v_fullHigh_4201_ = l_Lean_FileMap_leanPosToLspPos(v_text_4083_, v___y_4200_);
if (lean_obj_tag(v_endPos_4101_) == 0)
{
lean_dec_ref(v_pos_4100_);
lean_dec_ref(v_text_4083_);
lean_inc_ref(v_low_4190_);
v___y_4192_ = v_fullHigh_4201_;
v___y_4193_ = v_low_4190_;
goto v___jp_4191_;
}
else
{
if (v_keepFullRange_4102_ == 0)
{
lean_object* v_val_4202_; lean_object* v_line_4203_; lean_object* v_line_4204_; uint8_t v___x_4205_; 
v_val_4202_ = lean_ctor_get(v_endPos_4101_, 0);
lean_inc(v_val_4202_);
lean_dec_ref_known(v_endPos_4101_, 1);
v_line_4203_ = lean_ctor_get(v_pos_4100_, 0);
lean_inc(v_line_4203_);
lean_dec_ref(v_pos_4100_);
v_line_4204_ = lean_ctor_get(v_val_4202_, 0);
v___x_4205_ = lean_nat_dec_lt(v_line_4203_, v_line_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; 
lean_dec(v_line_4203_);
v___x_4206_ = l_Lean_FileMap_leanPosToLspPos(v_text_4083_, v_val_4202_);
v___y_4192_ = v_fullHigh_4201_;
v___y_4193_ = v___x_4206_;
goto v___jp_4191_;
}
else
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4217_; 
v_isSharedCheck_4217_ = !lean_is_exclusive(v_val_4202_);
if (v_isSharedCheck_4217_ == 0)
{
lean_object* v_unused_4218_; lean_object* v_unused_4219_; 
v_unused_4218_ = lean_ctor_get(v_val_4202_, 1);
lean_dec(v_unused_4218_);
v_unused_4219_ = lean_ctor_get(v_val_4202_, 0);
lean_dec(v_unused_4219_);
v___x_4208_ = v_val_4202_;
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v_val_4202_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4214_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
v___x_4211_ = lean_nat_add(v_line_4203_, v___x_4210_);
lean_dec(v_line_4203_);
v___x_4212_ = lean_unsigned_to_nat(0u);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 1, v___x_4212_);
lean_ctor_set(v___x_4208_, 0, v___x_4211_);
v___x_4214_ = v___x_4208_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_FileMap_leanPosToLspPos(v_text_4083_, v___x_4214_);
v___y_4192_ = v_fullHigh_4201_;
v___y_4193_ = v___x_4215_;
goto v___jp_4191_;
}
}
}
}
else
{
lean_object* v_val_4220_; lean_object* v___x_4221_; 
lean_dec_ref(v_pos_4100_);
v_val_4220_ = lean_ctor_get(v_endPos_4101_, 0);
lean_inc(v_val_4220_);
lean_dec_ref_known(v_endPos_4101_, 1);
v___x_4221_ = l_Lean_FileMap_leanPosToLspPos(v_text_4083_, v_val_4220_);
v___y_4192_ = v_fullHigh_4201_;
v___y_4193_ = v___x_4221_;
goto v___jp_4191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object* v_text_4223_, lean_object* v_m_4224_, lean_object* v_hasWidgets_4225_, lean_object* v_a_4226_){
_start:
{
uint8_t v_hasWidgets_boxed_4227_; lean_object* v_res_4228_; 
v_hasWidgets_boxed_4227_ = lean_unbox(v_hasWidgets_4225_);
v_res_4228_ = l_Lean_Widget_msgToInteractiveDiagnostic(v_text_4223_, v_m_4224_, v_hasWidgets_boxed_4227_);
return v_res_4228_;
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
