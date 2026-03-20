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
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_MessageData_maxTraceChildren;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_join(lean_object*);
extern lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Widget_tagCodeInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instInhabitedTaggedText_default(lean_object*);
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
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_InteractiveGoal_pretty(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
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
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object*);
uint8_t l_Lean_MessageData_isUnusedVariableWarning(lean_object*);
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64__value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object*);
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0_value;
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1_value;
static const lean_string_object l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2 = (const lean_object*)&l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17__value)}};
static const lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1 = (const lean_object*)&l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0 = (const lean_object*)&l_Lean_Widget_instRpcEncodableMsgEmbed___closed__0_value;
static const lean_closure_object l_Lean_Widget_instRpcEncodableMsgEmbed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57____boxed(lean_object*);
static const lean_closure_object l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__value;
LEAN_EXPORT const lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_ = (const lean_object*)&l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__value;
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
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown LeanDiagnosticTag"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown DiagnosticTag"};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default;
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object*);
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
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "MessageData.ofLazy: expected MessageData in Dynamic"};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6;
static const lean_string_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goal "};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__7_value)}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0_value;
static const lean_array_object l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1 = (const lean_object*)&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0;
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
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "goalsAccomplished"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 125, 130, 173, 238, 104, 164, 108)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value;
static const lean_string_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2 = (const lean_object*)&l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Widget_StrictOrLazy_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Widget_StrictOrLazy_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorIdx___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Widget_StrictOrLazy_ctorIdx(v_00_u03b1_10_, v_00_u03b2_11_, v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_t_14_);
v___x_17_ = lean_apply_1(v_k_15_, v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_ctorElim___boxed(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Widget_StrictOrLazy_ctorElim(v_00_u03b1_26_, v_00_u03b2_27_, v_motive_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim___redArg(lean_object* v_t_34_, lean_object* v_strict_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_34_, v_strict_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_strict_elim(lean_object* v_00_u03b1_37_, lean_object* v_00_u03b2_38_, lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_strict_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_40_, v_strict_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim___redArg(lean_object* v_t_44_, lean_object* v_lazy_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_44_, v_lazy_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_StrictOrLazy_lazy_elim(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_lazy_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Widget_StrictOrLazy_ctorElim___redArg(v_t_50_, v_lazy_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default___redArg(lean_object* v_inst_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v_inst_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default(lean_object* v_a_56_, lean_object* v_inst_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v_inst_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy___redArg(lean_object* v_inst_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_inst_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy(lean_object* v_a_62_, lean_object* v_inst_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v_inst_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx(lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(0u);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(1u);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorIdx(v_x_69_);
lean_dec_ref(v_x_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(lean_object* v_t_71_, lean_object* v_k_72_){
_start:
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v_t_71_);
v___x_74_ = lean_apply_1(v_k_72_, v_a_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim(lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_77_, v_k_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___boxed(lean_object* v_motive_81_, lean_object* v_ctorIdx_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_k_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim(v_motive_81_, v_ctorIdx_82_, v_t_83_, v_h_84_, v_k_85_);
lean_dec(v_ctorIdx_82_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object* v_t_87_, lean_object* v_Lean_Widget_RpcEncodablePacket_strict_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_87_, v_Lean_Widget_RpcEncodablePacket_strict_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_strict_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_Lean_Widget_RpcEncodablePacket_strict_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_91_, v_Lean_Widget_RpcEncodablePacket_strict_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim___redArg(lean_object* v_t_95_, lean_object* v_Lean_Widget_RpcEncodablePacket_lazy_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_95_, v_Lean_Widget_RpcEncodablePacket_lazy_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_lazy_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__elim(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_Lean_Widget_RpcEncodablePacket_lazy_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1__ctorElim___redArg(v_t_99_, v_Lean_Widget_RpcEncodablePacket_lazy_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(lean_object* v_json_111_){
_start:
{
lean_object* v___x_112_; 
lean_inc(v_json_111_);
v___x_112_ = l_Lean_Json_getTag_x3f(v_json_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; 
lean_dec(v_json_111_);
v___x_113_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_172_; 
v_val_114_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_172_ == 0)
{
v___x_116_ = v___x_112_;
v_isShared_117_ = v_isSharedCheck_172_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_dec(v___x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_172_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
v___x_120_ = lean_string_dec_eq(v_val_114_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
v___x_122_ = lean_string_dec_eq(v_val_114_, v___x_121_);
lean_dec(v_val_114_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_del_object(v___x_116_);
lean_dec(v_json_111_);
v___x_123_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_box(0);
v___x_126_ = l_Lean_Json_parseCtorFields(v_json_111_, v___x_121_, v___x_124_, v___x_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_del_object(v___x_116_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_147_; 
v_a_135_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_147_ == 0)
{
v___x_137_ = v___x_126_;
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_126_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_array_get(v___x_118_, v_a_135_, v___x_139_);
lean_dec(v_a_135_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 0);
lean_ctor_set(v___x_116_, 0, v___x_140_);
v___x_142_ = v___x_116_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_142_);
v___x_144_ = v___x_137_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_val_114_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_box(0);
v___x_150_ = l_Lean_Json_parseCtorFields(v_json_111_, v___x_119_, v___x_148_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_116_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_171_; 
v_a_159_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_171_ == 0)
{
v___x_161_ = v___x_150_;
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_150_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_array_get(v___x_118_, v_a_159_, v___x_163_);
lean_dec(v_a_159_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_164_);
v___x_166_ = v___x_116_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_166_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_a_176_ = lean_ctor_get(v_x_175_, 0);
v___x_177_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
lean_inc(v_a_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_176_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = l_Lean_Json_mkObj(v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_a_182_ = lean_ctor_get(v_x_175_, 0);
v___x_183_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_));
lean_inc(v_a_182_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_182_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = l_Lean_Json_mkObj(v___x_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37____boxed(lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v_x_188_);
lean_dec_ref(v_x_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_x_194_, lean_object* v_a_195_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_inst_193_);
v_a_196_ = lean_ctor_get(v_x_194_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_215_ == 0)
{
v___x_198_ = v_x_194_;
v_isShared_199_ = v_isSharedCheck_215_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v_x_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_215_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_rpcEncode_200_; lean_object* v___x_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_214_; 
v_rpcEncode_200_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_ref(v_rpcEncode_200_);
lean_dec_ref(v_inst_192_);
v___x_201_ = lean_apply_2(v_rpcEncode_200_, v_a_196_, v_a_195_);
v_fst_202_ = lean_ctor_get(v___x_201_, 0);
v_snd_203_ = lean_ctor_get(v___x_201_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_214_ == 0)
{
v___x_205_ = v___x_201_;
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_snd_203_);
lean_inc(v_fst_202_);
lean_dec(v___x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_fst_202_);
v___x_208_ = v___x_198_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_fst_202_);
v___x_208_ = v_reuseFailAlloc_213_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_208_);
lean_dec_ref(v___x_208_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_209_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_snd_203_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_inst_192_);
v_a_216_ = lean_ctor_get(v_x_194_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_194_);
if (v_isSharedCheck_235_ == 0)
{
v___x_218_ = v_x_194_;
v_isShared_219_ = v_isSharedCheck_235_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v_x_194_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_235_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_rpcEncode_220_; lean_object* v___x_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_234_; 
v_rpcEncode_220_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_rpcEncode_220_);
lean_dec_ref(v_inst_193_);
v___x_221_ = lean_apply_2(v_rpcEncode_220_, v_a_216_, v_a_195_);
v_fst_222_ = lean_ctor_get(v___x_221_, 0);
v_snd_223_ = lean_ctor_get(v___x_221_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_234_ == 0)
{
v___x_225_ = v___x_221_;
v_isShared_226_ = v_isSharedCheck_234_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_inc(v_fst_222_);
lean_dec(v___x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_234_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v_fst_222_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_fst_222_);
v___x_228_ = v_reuseFailAlloc_233_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_228_);
lean_dec_ref(v___x_228_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_229_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_snd_223_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_x_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_238_, v_inst_239_, v_x_240_, v_a_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_j_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_245_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_a_246_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
else
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_247_);
if (lean_obj_tag(v_a_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_inst_244_);
v_a_257_ = lean_ctor_get(v_a_256_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_282_ == 0)
{
v___x_259_ = v_a_256_;
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v_a_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_rpcDecode_261_; lean_object* v___x_262_; 
v_rpcDecode_261_ = lean_ctor_get(v_inst_243_, 1);
lean_inc_ref(v_rpcDecode_261_);
lean_dec_ref(v_inst_243_);
v___x_262_ = lean_apply_2(v_rpcDecode_261_, v_a_257_, v_a_246_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_del_object(v___x_259_);
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_281_; 
v_a_271_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_281_ == 0)
{
v___x_273_ = v___x_262_;
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_262_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v_a_271_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v_inst_243_);
v_a_283_ = lean_ctor_get(v_a_256_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_308_ == 0)
{
v___x_285_ = v_a_256_;
v_isShared_286_ = v_isSharedCheck_308_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_a_256_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_308_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_rpcDecode_287_; lean_object* v___x_288_; 
v_rpcDecode_287_ = lean_ctor_get(v_inst_244_, 1);
lean_inc_ref(v_rpcDecode_287_);
lean_dec_ref(v_inst_244_);
v___x_288_ = lean_apply_2(v_rpcDecode_287_, v_a_283_, v_a_246_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_del_object(v___x_285_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_a_297_);
v___x_302_ = v___x_285_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_00_u03b1_309_, lean_object* v_00_u03b2_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_j_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_311_, v_inst_312_, v_j_313_, v_a_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object* v_inst_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_inc_ref(v_inst_317_);
lean_inc_ref(v_inst_316_);
v___x_318_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_), 6, 4);
lean_closure_set(v___x_318_, 0, lean_box(0));
lean_closure_set(v___x_318_, 1, lean_box(0));
lean_closure_set(v___x_318_, 2, v_inst_316_);
lean_closure_set(v___x_318_, 3, v_inst_317_);
v___x_319_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_), 6, 4);
lean_closure_set(v___x_319_, 0, lean_box(0));
lean_closure_set(v___x_319_, 1, lean_box(0));
lean_closure_set(v___x_319_, 2, v_inst_316_);
lean_closure_set(v___x_319_, 3, v_inst_317_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(v_inst_323_, v_inst_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx(lean_object* v_x_335_){
_start:
{
switch(lean_obj_tag(v_x_335_))
{
case 0:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(0u);
return v___x_336_;
}
case 1:
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(1u);
return v___x_337_;
}
case 2:
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(2u);
return v___x_338_;
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(3u);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___boxed(lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Widget_MsgEmbed_ctorIdx(v_x_340_);
lean_dec_ref(v_x_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___redArg(lean_object* v_t_342_, lean_object* v_k_343_){
_start:
{
switch(lean_obj_tag(v_t_342_))
{
case 2:
{
lean_object* v_wi_344_; lean_object* v_alt_345_; lean_object* v___x_346_; 
v_wi_344_ = lean_ctor_get(v_t_342_, 0);
lean_inc_ref(v_wi_344_);
v_alt_345_ = lean_ctor_get(v_t_342_, 1);
lean_inc_ref(v_alt_345_);
lean_dec_ref(v_t_342_);
v___x_346_ = lean_apply_2(v_k_343_, v_wi_344_, v_alt_345_);
return v___x_346_;
}
case 3:
{
lean_object* v_indent_347_; lean_object* v_cls_348_; lean_object* v_msg_349_; uint8_t v_collapsed_350_; lean_object* v_children_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_indent_347_ = lean_ctor_get(v_t_342_, 0);
lean_inc(v_indent_347_);
v_cls_348_ = lean_ctor_get(v_t_342_, 1);
lean_inc(v_cls_348_);
v_msg_349_ = lean_ctor_get(v_t_342_, 2);
lean_inc_ref(v_msg_349_);
v_collapsed_350_ = lean_ctor_get_uint8(v_t_342_, sizeof(void*)*4);
v_children_351_ = lean_ctor_get(v_t_342_, 3);
lean_inc_ref(v_children_351_);
lean_dec_ref(v_t_342_);
v___x_352_ = lean_box(v_collapsed_350_);
v___x_353_ = lean_apply_5(v_k_343_, v_indent_347_, v_cls_348_, v_msg_349_, v___x_352_, v_children_351_);
return v___x_353_;
}
default: 
{
lean_object* v_a_354_; lean_object* v___x_355_; 
v_a_354_ = lean_ctor_get(v_t_342_, 0);
lean_inc_ref(v_a_354_);
lean_dec_ref(v_t_342_);
v___x_355_ = lean_apply_1(v_k_343_, v_a_354_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim(lean_object* v_motive__1_356_, lean_object* v_ctorIdx_357_, lean_object* v_t_358_, lean_object* v_h_359_, lean_object* v_k_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_358_, v_k_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___boxed(lean_object* v_motive__1_362_, lean_object* v_ctorIdx_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_k_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Widget_MsgEmbed_ctorElim(v_motive__1_362_, v_ctorIdx_363_, v_t_364_, v_h_365_, v_k_366_);
lean_dec(v_ctorIdx_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim___redArg(lean_object* v_t_368_, lean_object* v_expr_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_368_, v_expr_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim(lean_object* v_motive__1_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_expr_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_372_, v_expr_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim___redArg(lean_object* v_t_376_, lean_object* v_goal_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_376_, v_goal_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim(lean_object* v_motive__1_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_goal_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_380_, v_goal_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim___redArg(lean_object* v_t_384_, lean_object* v_widget_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_384_, v_widget_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim(lean_object* v_motive__1_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_widget_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_388_, v_widget_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim___redArg(lean_object* v_t_392_, lean_object* v_trace_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_392_, v_trace_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim(lean_object* v_motive__1_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_trace_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_396_, v_trace_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default(void){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Widget_instInhabitedMsgEmbed_default;
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx(lean_object* v_x_405_){
_start:
{
switch(lean_obj_tag(v_x_405_))
{
case 0:
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
return v___x_406_;
}
case 1:
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(1u);
return v___x_407_;
}
case 2:
{
lean_object* v___x_408_; 
v___x_408_ = lean_unsigned_to_nat(2u);
return v___x_408_;
}
default: 
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(3u);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx(v_x_410_);
lean_dec_ref(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(lean_object* v_t_412_, lean_object* v_k_413_){
_start:
{
switch(lean_obj_tag(v_t_412_))
{
case 2:
{
lean_object* v_wi_414_; lean_object* v_alt_415_; lean_object* v___x_416_; 
v_wi_414_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_wi_414_);
v_alt_415_ = lean_ctor_get(v_t_412_, 1);
lean_inc(v_alt_415_);
lean_dec_ref(v_t_412_);
v___x_416_ = lean_apply_2(v_k_413_, v_wi_414_, v_alt_415_);
return v___x_416_;
}
case 3:
{
lean_object* v_indent_417_; lean_object* v_cls_418_; lean_object* v_msg_419_; lean_object* v_collapsed_420_; lean_object* v_children_421_; lean_object* v___x_422_; 
v_indent_417_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_indent_417_);
v_cls_418_ = lean_ctor_get(v_t_412_, 1);
lean_inc(v_cls_418_);
v_msg_419_ = lean_ctor_get(v_t_412_, 2);
lean_inc(v_msg_419_);
v_collapsed_420_ = lean_ctor_get(v_t_412_, 3);
lean_inc(v_collapsed_420_);
v_children_421_ = lean_ctor_get(v_t_412_, 4);
lean_inc(v_children_421_);
lean_dec_ref(v_t_412_);
v___x_422_ = lean_apply_5(v_k_413_, v_indent_417_, v_cls_418_, v_msg_419_, v_collapsed_420_, v_children_421_);
return v___x_422_;
}
default: 
{
lean_object* v_a_423_; lean_object* v___x_424_; 
v_a_423_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v_t_412_);
v___x_424_ = lean_apply_1(v_k_413_, v_a_423_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(lean_object* v_motive_425_, lean_object* v_ctorIdx_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_k_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_427_, v_k_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___boxed(lean_object* v_motive_431_, lean_object* v_ctorIdx_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_k_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(v_motive_431_, v_ctorIdx_432_, v_t_433_, v_h_434_, v_k_435_);
lean_dec(v_ctorIdx_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_437_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_437_, v_Lean_Widget_RpcEncodablePacket_expr_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_441_, v_Lean_Widget_RpcEncodablePacket_expr_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_445_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_445_, v_Lean_Widget_RpcEncodablePacket_goal_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_449_, v_Lean_Widget_RpcEncodablePacket_goal_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_453_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_453_, v_Lean_Widget_RpcEncodablePacket_widget_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_456_, lean_object* v_t_457_, lean_object* v_h_458_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_457_, v_Lean_Widget_RpcEncodablePacket_widget_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_461_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_461_, v_Lean_Widget_RpcEncodablePacket_trace_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_464_, lean_object* v_t_465_, lean_object* v_h_466_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_465_, v_Lean_Widget_RpcEncodablePacket_trace_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(lean_object* v_json_520_){
_start:
{
lean_object* v___x_521_; 
lean_inc(v_json_520_);
v___x_521_ = l_Lean_Json_getTag_x3f(v_json_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
lean_dec(v_json_520_);
v___x_522_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_522_;
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_639_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_639_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_639_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_639_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_box(0);
v___x_528_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_529_ = lean_string_dec_eq(v_val_523_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_531_ = lean_string_dec_eq(v_val_523_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
lean_del_object(v___x_525_);
v___x_532_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_533_ = lean_string_dec_eq(v_val_523_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_535_ = lean_string_dec_eq(v_val_523_, v___x_534_);
lean_dec(v_val_523_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v_json_520_);
v___x_536_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_unsigned_to_nat(5u);
v___x_538_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_539_ = l_Lean_Json_parseCtorFields(v_json_520_, v___x_534_, v___x_537_, v___x_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_566_; 
v_a_548_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_566_ == 0)
{
v___x_550_ = v___x_539_;
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_539_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_get(v___x_527_, v_a_548_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_array_get(v___x_527_, v_a_548_, v___x_554_);
v___x_556_ = lean_unsigned_to_nat(2u);
v___x_557_ = lean_array_get(v___x_527_, v_a_548_, v___x_556_);
v___x_558_ = lean_unsigned_to_nat(3u);
v___x_559_ = lean_array_get(v___x_527_, v_a_548_, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_array_get(v___x_527_, v_a_548_, v___x_560_);
lean_dec(v_a_548_);
v___x_562_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_562_, 0, v___x_553_);
lean_ctor_set(v___x_562_, 1, v___x_555_);
lean_ctor_set(v___x_562_, 2, v___x_557_);
lean_ctor_set(v___x_562_, 3, v___x_559_);
lean_ctor_set(v___x_562_, 4, v___x_561_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_562_);
v___x_564_ = v___x_550_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_val_523_);
v___x_567_ = lean_unsigned_to_nat(2u);
v___x_568_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_569_ = l_Lean_Json_parseCtorFields(v_json_520_, v___x_532_, v___x_567_, v___x_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_590_; 
v_a_578_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_590_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_array_get(v___x_527_, v_a_578_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_array_get(v___x_527_, v_a_578_, v___x_584_);
lean_dec(v_a_578_);
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_583_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_586_);
v___x_588_ = v___x_580_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_val_523_);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_box(0);
v___x_593_ = l_Lean_Json_parseCtorFields(v_json_520_, v___x_530_, v___x_591_, v___x_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_del_object(v___x_525_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_614_; 
v_a_602_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_614_ == 0)
{
v___x_604_ = v___x_593_;
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_593_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_array_get(v___x_527_, v_a_602_, v___x_606_);
lean_dec(v_a_602_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
lean_ctor_set(v___x_525_, 0, v___x_607_);
v___x_609_ = v___x_525_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_609_);
v___x_611_ = v___x_604_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v_val_523_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_box(0);
v___x_617_ = l_Lean_Json_parseCtorFields(v_json_520_, v___x_528_, v___x_615_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_del_object(v___x_525_);
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_638_; 
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_638_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get(v___x_527_, v_a_626_, v___x_630_);
lean_dec(v_a_626_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_631_);
v___x_633_ = v___x_525_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_633_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(lean_object* v_x_642_){
_start:
{
switch(lean_obj_tag(v_x_642_))
{
case 0:
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_a_643_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v_x_642_);
v___x_644_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_a_643_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_Json_mkObj(v___x_647_);
return v___x_648_;
}
case 1:
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_a_649_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v_x_642_);
v___x_650_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_a_649_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_Json_mkObj(v___x_653_);
return v___x_654_;
}
case 2:
{
lean_object* v_wi_655_; lean_object* v_alt_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_674_; 
v_wi_655_ = lean_ctor_get(v_x_642_, 0);
v_alt_656_ = lean_ctor_get(v_x_642_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_674_ == 0)
{
v___x_658_ = v_x_642_;
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_alt_656_);
lean_inc(v_wi_655_);
lean_dec(v_x_642_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_661_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 0);
lean_ctor_set(v___x_658_, 1, v_wi_655_);
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_wi_655_);
v___x_663_ = v_reuseFailAlloc_673_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_664_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_alt_656_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_Json_mkObj(v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_660_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_666_);
v___x_672_ = l_Lean_Json_mkObj(v___x_671_);
return v___x_672_;
}
}
}
default: 
{
lean_object* v_indent_675_; lean_object* v_cls_676_; lean_object* v_msg_677_; lean_object* v_collapsed_678_; lean_object* v_children_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_indent_675_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_indent_675_);
v_cls_676_ = lean_ctor_get(v_x_642_, 1);
lean_inc(v_cls_676_);
v_msg_677_ = lean_ctor_get(v_x_642_, 2);
lean_inc(v_msg_677_);
v_collapsed_678_ = lean_ctor_get(v_x_642_, 3);
lean_inc(v_collapsed_678_);
v_children_679_ = lean_ctor_get(v_x_642_, 4);
lean_inc(v_children_679_);
lean_dec_ref(v_x_642_);
v___x_680_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_681_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_indent_675_);
v___x_683_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_cls_676_);
v___x_685_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_msg_677_);
v___x_687_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_collapsed_678_);
v___x_689_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_children_679_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_688_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_686_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_684_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_682_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_Json_mkObj(v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_680_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_691_);
v___x_700_ = l_Lean_Json_mkObj(v___x_699_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t v_sz_703_, size_t v_i_704_, lean_object* v_bs_705_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_706_ == 0)
{
return v_bs_705_;
}
else
{
lean_object* v_v_707_; lean_object* v___x_708_; lean_object* v_bs_x27_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v_v_707_ = lean_array_uget(v_bs_705_, v_i_704_);
v___x_708_ = lean_unsigned_to_nat(0u);
v_bs_x27_709_ = lean_array_uset(v_bs_705_, v_i_704_, v___x_708_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_add(v_i_704_, v___x_710_);
v___x_712_ = lean_array_uset(v_bs_x27_709_, v_i_704_, v_v_707_);
v_i_704_ = v___x_711_;
v_bs_705_ = v___x_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object* v_sz_714_, lean_object* v_i_715_, lean_object* v_bs_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_714_);
lean_dec(v_sz_714_);
v_i_boxed_718_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_boxed_717_, v_i_boxed_718_, v_bs_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object* v_a_720_){
_start:
{
size_t v_sz_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_sz_721_ = lean_array_size(v_a_720_);
v___x_722_ = ((size_t)0ULL);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_721_, v___x_722_, v_a_720_);
v___x_724_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object* v_x_728_){
_start:
{
switch(lean_obj_tag(v_x_728_))
{
case 0:
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_741_; 
v_a_729_ = lean_ctor_get(v_x_728_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_731_ = v_x_728_;
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v_x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 3);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_729_);
v___x_735_ = v_reuseFailAlloc_740_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_Json_mkObj(v___x_738_);
return v___x_739_;
}
}
}
case 1:
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_742_ = lean_ctor_get(v_x_728_, 0);
lean_inc_ref(v_a_742_);
lean_dec_ref(v_x_728_);
v___x_743_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_744_ = l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(v_a_742_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_Json_mkObj(v___x_747_);
return v___x_748_;
}
default: 
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_767_; 
v_a_749_ = lean_ctor_get(v_x_728_, 0);
v_a_750_ = lean_ctor_get(v_x_728_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_767_ == 0)
{
v___x_752_ = v_x_728_;
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_inc(v_a_749_);
lean_dec(v_x_728_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_754_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_755_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_a_750_);
v___x_756_ = lean_unsigned_to_nat(2u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_array_push(v___x_757_, v_a_749_);
v___x_759_ = lean_array_push(v___x_758_, v___x_755_);
v___x_760_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
lean_ctor_set(v___x_752_, 1, v___x_760_);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_762_ = v___x_752_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_Json_mkObj(v___x_764_);
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t v_sz_768_, size_t v_i_769_, lean_object* v_bs_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_769_, v_sz_768_);
if (v___x_771_ == 0)
{
return v_bs_770_;
}
else
{
lean_object* v_v_772_; lean_object* v___x_773_; lean_object* v_bs_x27_774_; lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_v_772_ = lean_array_uget(v_bs_770_, v_i_769_);
v___x_773_ = lean_unsigned_to_nat(0u);
v_bs_x27_774_ = lean_array_uset(v_bs_770_, v_i_769_, v___x_773_);
v___x_775_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_v_772_);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_769_, v___x_776_);
v___x_778_ = lean_array_uset(v_bs_x27_774_, v_i_769_, v___x_775_);
v_i_769_ = v___x_777_;
v_bs_770_ = v___x_778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object* v_a_780_){
_start:
{
size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_sz_781_ = lean_array_size(v_a_780_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_781_, v___x_782_, v_a_780_);
v___x_784_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object* v_sz_785_, lean_object* v_i_786_, lean_object* v_bs_787_){
_start:
{
size_t v_sz_boxed_788_; size_t v_i_boxed_789_; lean_object* v_res_790_; 
v_sz_boxed_788_ = lean_unbox_usize(v_sz_785_);
lean_dec(v_sz_785_);
v_i_boxed_789_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_boxed_788_, v_i_boxed_789_, v_bs_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(lean_object* v_f_791_, lean_object* v_x_792_, lean_object* v___y_793_){
_start:
{
switch(lean_obj_tag(v_x_792_))
{
case 0:
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_f_791_);
v_a_794_ = lean_ctor_get(v_x_792_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v_x_792_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v_x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___y_793_);
return v___x_800_;
}
}
}
case 1:
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_822_; 
v_a_803_ = lean_ctor_get(v_x_792_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_822_ == 0)
{
v___x_805_ = v_x_792_;
v_isShared_806_ = v_isSharedCheck_822_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v_x_792_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_822_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_821_; 
v_sz_807_ = lean_array_size(v_a_803_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_791_, v_sz_807_, v___x_808_, v_a_803_, v___y_793_);
v_fst_810_ = lean_ctor_get(v___x_809_, 0);
v_snd_811_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_821_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snd_811_);
lean_inc(v_fst_810_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_fst_810_);
v___x_816_ = v___x_805_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_810_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_snd_811_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
default: 
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_a_823_ = lean_ctor_get(v_x_792_, 0);
v_a_824_ = lean_ctor_get(v_x_792_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v_x_792_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_inc(v_a_823_);
lean_dec(v_x_792_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v___x_831_; lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_843_; 
lean_inc_ref(v_f_791_);
v___x_828_ = lean_apply_2(v_f_791_, v_a_823_, v___y_793_);
v_fst_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_fst_829_);
v_snd_830_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_snd_830_);
lean_dec_ref(v___x_828_);
v___x_831_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_791_, v_a_824_, v_snd_830_);
v_fst_832_ = lean_ctor_get(v___x_831_, 0);
v_snd_833_ = lean_ctor_get(v___x_831_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_843_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snd_833_);
lean_inc(v_fst_832_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_843_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_fst_832_);
lean_ctor_set(v___x_826_, 0, v_fst_829_);
v___x_838_ = v___x_826_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_fst_832_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_snd_833_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(lean_object* v_f_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_bs_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_f_845_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_bs_848_);
lean_ctor_set(v___x_851_, 1, v___y_849_);
return v___x_851_;
}
else
{
lean_object* v_v_852_; lean_object* v___x_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_856_; lean_object* v_bs_x27_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v_v_852_ = lean_array_uget_borrowed(v_bs_848_, v_i_847_);
lean_inc(v_v_852_);
lean_inc_ref(v_f_845_);
v___x_853_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_845_, v_v_852_, v___y_849_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_fst_854_);
v_snd_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_snd_855_);
lean_dec_ref(v___x_853_);
v___x_856_ = lean_unsigned_to_nat(0u);
v_bs_x27_857_ = lean_array_uset(v_bs_848_, v_i_847_, v___x_856_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_847_, v___x_858_);
v___x_860_ = lean_array_uset(v_bs_x27_857_, v_i_847_, v_fst_854_);
v_i_847_ = v___x_859_;
v_bs_848_ = v___x_860_;
v___y_849_ = v_snd_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg___boxed(lean_object* v_f_862_, lean_object* v_sz_863_, lean_object* v_i_864_, lean_object* v_bs_865_, lean_object* v___y_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_863_);
lean_dec(v_sz_863_);
v_i_boxed_868_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_862_, v_sz_boxed_867_, v_i_boxed_868_, v_bs_865_, v___y_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(lean_object* v_x_871_, lean_object* v_a_872_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_894_; 
v_a_873_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_894_ == 0)
{
v___x_875_ = v_x_871_;
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_894_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_sz_877_ = lean_array_size(v_a_873_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_877_, v___x_878_, v_a_873_, v_a_872_);
v_fst_880_ = lean_ctor_get(v___x_879_, 0);
v_snd_881_ = lean_ctor_get(v___x_879_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v___x_879_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_inc(v_fst_880_);
lean_dec(v___x_879_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(v_fst_880_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_885_);
v___x_887_ = v___x_875_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_892_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_887_);
lean_dec_ref(v___x_887_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_888_);
v___x_890_ = v___x_883_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_881_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_914_; 
v_a_895_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_914_ == 0)
{
v___x_897_ = v_x_871_;
v_isShared_898_ = v_isSharedCheck_914_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v_x_871_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_914_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_fst_901_; lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v___x_899_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_900_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_899_, v_a_895_, v_a_872_);
lean_dec(v_a_895_);
v_fst_901_ = lean_ctor_get(v___x_900_, 0);
v_snd_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_inc(v_fst_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_fst_901_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fst_901_);
v___x_907_ = v_reuseFailAlloc_912_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_907_);
lean_dec_ref(v___x_907_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_908_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_snd_902_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_x_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
switch(lean_obj_tag(v_x_915_))
{
case 0:
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v___x_917_);
v_a_918_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_938_ == 0)
{
v___x_920_ = v_x_915_;
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v_x_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_938_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v___x_922_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_923_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_922_, v_a_918_, v_a_916_);
v_fst_924_ = lean_ctor_get(v___x_923_, 0);
v_snd_925_ = lean_ctor_get(v___x_923_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_924_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_929_);
v___x_931_ = v___x_920_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_931_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_932_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_925_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
case 1:
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___x_917_);
v_a_939_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_957_ == 0)
{
v___x_941_ = v_x_915_;
v_isShared_942_ = v_isSharedCheck_957_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_x_915_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_957_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_956_; 
v___x_943_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_939_, v_a_916_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
v_snd_945_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_956_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_944_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_fst_944_);
v___x_950_ = v___x_941_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_fst_944_);
v___x_950_ = v_reuseFailAlloc_955_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_950_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_snd_945_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
case 2:
{
lean_object* v_wi_958_; lean_object* v_alt_959_; lean_object* v___x_960_; lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_981_; 
v_wi_958_ = lean_ctor_get(v_x_915_, 0);
lean_inc_ref(v_wi_958_);
v_alt_959_ = lean_ctor_get(v_x_915_, 1);
lean_inc_ref(v_alt_959_);
lean_dec_ref(v_x_915_);
v___x_960_ = l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_958_, v_a_916_);
v_fst_961_ = lean_ctor_get(v___x_960_, 0);
v_snd_962_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_981_ == 0)
{
v___x_964_ = v___x_960_;
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v___x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_980_; 
v___x_966_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_917_, v_alt_959_, v_snd_962_);
v_fst_967_ = lean_ctor_get(v___x_966_, 0);
v_snd_968_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_980_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_snd_968_);
lean_inc(v_fst_967_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_980_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_967_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 2);
lean_ctor_set(v___x_964_, 1, v___x_972_);
v___x_974_ = v___x_964_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_979_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_974_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_975_);
v___x_977_ = v___x_970_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_snd_968_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
default: 
{
lean_object* v_indent_982_; lean_object* v_cls_983_; lean_object* v_msg_984_; uint8_t v_collapsed_985_; lean_object* v_children_986_; lean_object* v___x_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_990_; lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1008_; 
v_indent_982_ = lean_ctor_get(v_x_915_, 0);
lean_inc(v_indent_982_);
v_cls_983_ = lean_ctor_get(v_x_915_, 1);
lean_inc(v_cls_983_);
v_msg_984_ = lean_ctor_get(v_x_915_, 2);
lean_inc_ref(v_msg_984_);
v_collapsed_985_ = lean_ctor_get_uint8(v_x_915_, sizeof(void*)*4);
v_children_986_ = lean_ctor_get(v_x_915_, 3);
lean_inc_ref(v_children_986_);
lean_dec_ref(v_x_915_);
v___x_987_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_917_, v_msg_984_, v_a_916_);
v_fst_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_fst_988_);
v_snd_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_987_);
v___x_990_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(v_children_986_, v_snd_989_);
v_fst_991_ = lean_ctor_get(v___x_990_, 0);
v_snd_992_ = lean_ctor_get(v___x_990_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_1008_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_inc(v_fst_991_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1008_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_996_ = l_Lean_JsonNumber_fromNat(v_indent_982_);
v___x_997_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___x_998_ = 1;
v___x_999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_cls_983_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
v___x_1001_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_988_);
v___x_1002_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1002_, 0, v_collapsed_985_);
v___x_1003_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_1000_);
lean_ctor_set(v___x_1003_, 2, v___x_1001_);
lean_ctor_set(v___x_1003_, 3, v___x_1002_);
lean_ctor_set(v___x_1003_, 4, v_fst_991_);
v___x_1004_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_1003_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1004_);
v___x_1006_ = v___x_994_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_snd_992_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_bs_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_bs_1011_);
lean_ctor_set(v___x_1014_, 1, v___y_1012_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v_v_1016_; lean_object* v___x_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1020_; lean_object* v_bs_x27_1021_; lean_object* v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1015_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
v_v_1016_ = lean_array_uget_borrowed(v_bs_1011_, v_i_1010_);
lean_inc(v_v_1016_);
v___x_1017_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_1015_, v_v_1016_, v___y_1012_);
v_fst_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_fst_1018_);
v_snd_1019_ = lean_ctor_get(v___x_1017_, 1);
lean_inc(v_snd_1019_);
lean_dec_ref(v___x_1017_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v_bs_x27_1021_ = lean_array_uset(v_bs_1011_, v_i_1010_, v___x_1020_);
v___x_1022_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_1018_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1010_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1021_, v_i_1010_, v___x_1022_);
v_i_1010_ = v___x_1024_;
v_bs_1011_ = v___x_1025_;
v___y_1012_ = v_snd_1019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_boxed_1031_, v_i_boxed_1032_, v_bs_1029_, v___y_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(lean_object* v_x_1034_){
_start:
{
lean_inc_ref(v_x_1034_);
return v_x_1034_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg___boxed(lean_object* v_x_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(v_x_1035_);
lean_dec_ref(v_x_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(lean_object* v_00_u03b1_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_){
_start:
{
lean_inc_ref(v_x_1038_);
return v_x_1038_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(v_00_u03b1_1040_, v_x_1041_, v___y_1042_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_x_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object* v_json_1050_){
_start:
{
lean_object* v___x_1051_; 
lean_inc(v_json_1050_);
v___x_1051_ = l_Lean_Json_getTag_x3f(v_json_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_json_1050_);
v___x_1052_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0));
return v___x_1052_;
}
else
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1159_; 
v_val_1053_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1055_ = v___x_1051_;
v_isShared_1056_ = v_isSharedCheck_1159_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1159_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_1059_ = lean_string_dec_eq(v_val_1053_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
v___x_1061_ = lean_string_dec_eq(v_val_1053_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
lean_del_object(v___x_1055_);
v___x_1062_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_1063_ = lean_string_dec_eq(v_val_1053_, v___x_1062_);
lean_dec(v_val_1053_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec(v_json_1050_);
v___x_1064_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1));
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_unsigned_to_nat(2u);
v___x_1066_ = lean_box(0);
v___x_1067_ = l_Lean_Json_parseCtorFields(v_json_1050_, v___x_1062_, v___x_1065_, v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_a_1076_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1067_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_array_get(v___x_1057_, v_a_1076_, v___x_1077_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_array_get(v___x_1057_, v_a_1076_, v___x_1079_);
lean_dec(v_a_1076_);
v___x_1081_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_dec(v___x_1078_);
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1078_);
lean_ctor_set(v___x_1086_, 1, v_a_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_val_1053_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_box(0);
v___x_1093_ = l_Lean_Json_parseCtorFields(v_json_1050_, v___x_1060_, v___x_1091_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1055_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1093_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_array_get(v___x_1057_, v_a_1102_, v___x_1103_);
lean_dec(v_a_1102_);
v___x_1105_ = l_Lean_Json_getStr_x3f(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_del_object(v___x_1055_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1124_; 
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1114_);
v___x_1119_ = v___x_1055_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1119_);
v___x_1121_ = v___x_1116_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_val_1053_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Lean_Json_parseCtorFields(v_json_1050_, v___x_1058_, v___x_1125_, v___x_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1055_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1136_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1127_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_array_get(v___x_1057_, v_a_1136_, v___x_1137_);
lean_dec(v_a_1136_);
v___x_1139_ = l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1055_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1158_; 
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1148_);
v___x_1153_ = v___x_1055_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t v_sz_1160_, size_t v_i_1161_, lean_object* v_bs_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1161_, v_sz_1160_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_bs_1162_);
return v___x_1164_;
}
else
{
lean_object* v_v_1165_; lean_object* v___x_1166_; 
v_v_1165_ = lean_array_uget_borrowed(v_bs_1162_, v_i_1161_);
lean_inc(v_v_1165_);
v___x_1166_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1165_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_bs_1162_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v_bs_x27_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_a_1175_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1166_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v_bs_x27_1177_ = lean_array_uset(v_bs_1162_, v_i_1161_, v___x_1176_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1161_, v___x_1178_);
v___x_1180_ = lean_array_uset(v_bs_x27_1177_, v_i_1161_, v_a_1175_);
v_i_1161_ = v___x_1179_;
v_bs_1162_ = v___x_1180_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object* v_x_1182_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 4)
{
lean_object* v_elems_1183_; size_t v_sz_1184_; size_t v___x_1185_; lean_object* v___x_1186_; 
v_elems_1183_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_elems_1183_);
lean_dec_ref(v_x_1182_);
v_sz_1184_ = lean_array_size(v_elems_1183_);
v___x_1185_ = ((size_t)0ULL);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_1184_, v___x_1185_, v_elems_1183_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1187_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1188_ = lean_unsigned_to_nat(80u);
v___x_1189_ = l_Lean_Json_pretty(v_x_1182_, v___x_1188_);
v___x_1190_ = lean_string_append(v___x_1187_, v___x_1189_);
lean_dec_ref(v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1192_ = lean_string_append(v___x_1190_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object* v_sz_1194_, lean_object* v_i_1195_, lean_object* v_bs_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1194_);
lean_dec(v_sz_1194_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1195_);
lean_dec(v_i_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_boxed_1197_, v_i_boxed_1198_, v_bs_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object* v_f_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_){
_start:
{
switch(lean_obj_tag(v_x_1201_))
{
case 0:
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_f_1200_);
v_a_1203_ = lean_ctor_get(v_x_1201_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1201_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v_x_1201_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v_x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
case 1:
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1238_; 
v_a_1212_ = lean_ctor_get(v_x_1201_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1201_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1214_ = v_x_1201_;
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v_x_1201_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v_sz_1216_ = lean_array_size(v_a_1212_);
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1200_, v_sz_1216_, v___x_1217_, v_a_1212_, v___y_1202_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1214_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1237_; 
v_a_1227_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1229_ = v___x_1218_;
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1218_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_a_1227_);
v___x_1232_ = v___x_1214_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
default: 
{
lean_object* v_a_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1266_; 
v_a_1239_ = lean_ctor_get(v_x_1201_, 0);
v_a_1240_ = lean_ctor_get(v_x_1201_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1201_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1242_ = v_x_1201_;
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_inc(v_a_1239_);
lean_dec(v_x_1201_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; 
lean_inc_ref(v_f_1200_);
lean_inc_ref(v___y_1202_);
v___x_1244_ = lean_apply_2(v_f_1200_, v_a_1239_, v___y_1202_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_f_1200_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1244_);
v___x_1254_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1200_, v_a_1240_, v___y_1202_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec(v_a_1253_);
lean_del_object(v___x_1242_);
return v___x_1254_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_a_1255_);
lean_ctor_set(v___x_1242_, 0, v_a_1253_);
v___x_1260_ = v___x_1242_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object* v_f_1267_, size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_bs_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v___y_1271_);
lean_dec_ref(v_f_1267_);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_bs_1270_);
return v___x_1273_;
}
else
{
lean_object* v_v_1274_; lean_object* v___x_1275_; 
v_v_1274_ = lean_array_uget_borrowed(v_bs_1270_, v_i_1269_);
lean_inc_ref(v___y_1271_);
lean_inc(v_v_1274_);
lean_inc_ref(v_f_1267_);
v___x_1275_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1267_, v_v_1274_, v___y_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v___y_1271_);
lean_dec_ref(v_bs_1270_);
lean_dec_ref(v_f_1267_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v_bs_x27_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1275_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v_bs_x27_1286_ = lean_array_uset(v_bs_1270_, v_i_1269_, v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_i_1269_, v___x_1287_);
v___x_1289_ = lean_array_uset(v_bs_x27_1286_, v_i_1269_, v_a_1284_);
v_i_1269_ = v___x_1288_;
v_bs_1270_ = v___x_1289_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object* v_f_1291_, lean_object* v_sz_1292_, lean_object* v_i_1293_, lean_object* v_bs_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_sz_boxed_1296_; size_t v_i_boxed_1297_; lean_object* v_res_1298_; 
v_sz_boxed_1296_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1297_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1291_, v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1294_, v___y_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_bs_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_bs_1301_);
return v___x_1303_;
}
else
{
lean_object* v_v_1304_; lean_object* v___x_1305_; lean_object* v_bs_x27_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v_v_1304_ = lean_array_uget(v_bs_1301_, v_i_1300_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v_bs_x27_1306_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1305_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_add(v_i_1300_, v___x_1307_);
v___x_1309_ = lean_array_uset(v_bs_x27_1306_, v_i_1300_, v_v_1304_);
v_i_1300_ = v___x_1308_;
v_bs_1301_ = v___x_1309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object* v_sz_1311_, lean_object* v_i_1312_, lean_object* v_bs_1313_){
_start:
{
size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_boxed_1314_, v_i_boxed_1315_, v_bs_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 4)
{
lean_object* v_elems_1318_; size_t v_sz_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v_elems_1318_ = lean_ctor_get(v_x_1317_, 0);
lean_inc_ref(v_elems_1318_);
lean_dec_ref(v_x_1317_);
v_sz_1319_ = lean_array_size(v_elems_1318_);
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_1319_, v___x_1320_, v_elems_1318_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1322_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1323_ = lean_unsigned_to_nat(80u);
v___x_1324_ = l_Lean_Json_pretty(v_x_1317_, v___x_1323_);
v___x_1325_ = lean_string_append(v___x_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object* v_j_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_1330_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_a_1331_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; 
v_a_1341_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1332_);
if (lean_obj_tag(v_a_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1378_; 
v_a_1342_ = lean_ctor_get(v_a_1341_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1344_ = v_a_1341_;
v_isShared_1345_ = v_isSharedCheck_1378_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v_a_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1378_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(v_a_1342_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_del_object(v___x_1344_);
lean_dec_ref(v_a_1331_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v_a_1355_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1346_);
v_sz_1356_ = lean_array_size(v_a_1355_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_1356_, v___x_1357_, v_a_1355_, v_a_1331_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_del_object(v___x_1344_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
v_a_1367_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v_a_1367_);
v___x_1372_ = v___x_1344_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1404_; 
v_a_1379_ = lean_ctor_get(v_a_1341_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1381_ = v_a_1341_;
v_isShared_1382_ = v_isSharedCheck_1404_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v_a_1341_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1404_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_1384_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_1383_, v_a_1379_, v_a_1331_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_del_object(v___x_1381_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1403_; 
v_a_1393_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1395_ = v___x_1384_;
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1384_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1403_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_a_1393_);
v___x_1398_ = v___x_1381_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_j_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(v_j_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_a_1406_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1407_);
v___x_1417_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
switch(lean_obj_tag(v_a_1416_))
{
case 0:
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v___x_1417_);
v_a_1418_ = lean_ctor_get(v_a_1416_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1420_ = v_a_1416_;
v_isShared_1421_ = v_isSharedCheck_1453_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v_a_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1453_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_a_1418_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1420_);
lean_dec_ref(v_a_1406_);
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
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1422_);
v___x_1432_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_1433_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1432_, v_a_1431_, v_a_1406_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_del_object(v___x_1420_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1452_; 
v_a_1442_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1444_ = v___x_1433_;
v_isShared_1445_ = v_isSharedCheck_1452_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1433_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1452_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v_a_1442_);
v___x_1447_ = v___x_1420_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___x_1417_);
v_a_1454_ = lean_ctor_get(v_a_1416_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1456_ = v_a_1416_;
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v_a_1416_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_1454_, v_a_1406_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_del_object(v___x_1456_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1477_; 
v_a_1467_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1469_ = v___x_1458_;
v_isShared_1470_ = v_isSharedCheck_1477_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1458_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1477_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v_a_1467_);
v___x_1472_ = v___x_1456_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1472_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
case 2:
{
lean_object* v_wi_1479_; lean_object* v_alt_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1524_; 
v_wi_1479_ = lean_ctor_get(v_a_1416_, 0);
v_alt_1480_ = lean_ctor_get(v_a_1416_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1482_ = v_a_1416_;
v_isShared_1483_ = v_isSharedCheck_1524_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_alt_1480_);
lean_inc(v_wi_1479_);
lean_dec(v_a_1416_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1524_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_1479_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_del_object(v___x_1482_);
lean_dec(v_alt_1480_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_a_1406_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1484_);
v___x_1494_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_alt_1480_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_a_1493_);
lean_del_object(v___x_1482_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_a_1406_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1494_);
v___x_1504_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1417_, v_a_1503_, v_a_1406_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1493_);
lean_del_object(v___x_1482_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_a_1513_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1515_ = v___x_1504_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1504_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v_a_1513_);
lean_ctor_set(v___x_1482_, 0, v_a_1493_);
v___x_1518_ = v___x_1482_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1493_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
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
lean_object* v_indent_1525_; lean_object* v_cls_1526_; lean_object* v_msg_1527_; lean_object* v_collapsed_1528_; lean_object* v_children_1529_; lean_object* v___x_1530_; 
v_indent_1525_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_indent_1525_);
v_cls_1526_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_cls_1526_);
v_msg_1527_ = lean_ctor_get(v_a_1416_, 2);
lean_inc(v_msg_1527_);
v_collapsed_1528_ = lean_ctor_get(v_a_1416_, 3);
lean_inc(v_collapsed_1528_);
v_children_1529_ = lean_ctor_get(v_a_1416_, 4);
lean_inc(v_children_1529_);
lean_dec_ref(v_a_1416_);
v___x_1530_ = l_Lean_Json_getNat_x3f(v_indent_1525_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_children_1529_);
lean_dec(v_collapsed_1528_);
lean_dec(v_msg_1527_);
lean_dec(v_cls_1526_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_a_1406_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1530_);
v___x_1540_ = l_Lean_Name_fromJson_x3f(v_cls_1526_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1539_);
lean_dec(v_children_1529_);
lean_dec(v_collapsed_1528_);
lean_dec(v_msg_1527_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_a_1406_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1540_);
v___x_1550_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_msg_1527_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_a_1549_);
lean_dec(v_a_1539_);
lean_dec(v_children_1529_);
lean_dec(v_collapsed_1528_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_a_1406_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1550_);
lean_inc_ref(v_a_1406_);
v___x_1560_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1417_, v_a_1559_, v_a_1406_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_a_1549_);
lean_dec(v_a_1539_);
lean_dec(v_children_1529_);
lean_dec(v_collapsed_1528_);
lean_dec_ref(v_a_1406_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1560_);
v___x_1570_ = l_Lean_Json_getBool_x3f(v_collapsed_1528_);
lean_dec(v_collapsed_1528_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1569_);
lean_dec(v_a_1549_);
lean_dec(v_a_1539_);
lean_dec(v_children_1529_);
lean_dec_ref(v_a_1406_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1570_);
v___x_1580_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_children_1529_, v_a_1406_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1579_);
lean_dec(v_a_1569_);
lean_dec(v_a_1549_);
lean_dec(v_a_1539_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1598_; 
v_a_1589_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1591_ = v___x_1580_;
v_isShared_1592_ = v_isSharedCheck_1598_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1580_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1598_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; uint8_t v___x_1594_; lean_object* v___x_1596_; 
v___x_1593_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_1593_, 0, v_a_1539_);
lean_ctor_set(v___x_1593_, 1, v_a_1549_);
lean_ctor_set(v___x_1593_, 2, v_a_1569_);
lean_ctor_set(v___x_1593_, 3, v_a_1589_);
v___x_1594_ = lean_unbox(v_a_1579_);
lean_dec(v_a_1579_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*4, v___x_1594_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1593_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t v_sz_1599_, size_t v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1600_, v_sz_1599_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec_ref(v___y_1602_);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_bs_1601_);
return v___x_1604_;
}
else
{
lean_object* v_v_1605_; lean_object* v___x_1606_; 
v_v_1605_ = lean_array_uget_borrowed(v_bs_1601_, v_i_1600_);
lean_inc(v_v_1605_);
v___x_1606_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_bs_1601_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1606_);
v___x_1616_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
lean_inc_ref(v___y_1602_);
v___x_1617_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1616_, v_a_1615_, v___y_1602_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_bs_1601_);
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
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v_bs_x27_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v_a_1626_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1617_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v_bs_x27_1628_ = lean_array_uset(v_bs_1601_, v_i_1600_, v___x_1627_);
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1600_, v___x_1629_);
v___x_1631_ = lean_array_uset(v_bs_x27_1628_, v_i_1600_, v_a_1626_);
v_i_1600_ = v___x_1630_;
v_bs_1601_ = v___x_1631_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14___boxed(lean_object* v_sz_1633_, lean_object* v_i_1634_, lean_object* v_bs_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_sz_boxed_1637_; size_t v_i_boxed_1638_; lean_object* v_res_1639_; 
v_sz_boxed_1637_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1638_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_boxed_1637_, v_i_boxed_1638_, v_bs_1635_, v___y_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_f_1642_, lean_object* v_x_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_1642_, v_x_1643_, v___y_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5(lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_f_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1648_, v_x_1649_, v___y_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object* v_00_u03b1_1652_, lean_object* v_00_u03b2_1653_, lean_object* v_f_1654_, size_t v_sz_1655_, size_t v_i_1656_, lean_object* v_bs_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_1654_, v_sz_1655_, v_i_1656_, v_bs_1657_, v___y_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_f_1662_, lean_object* v_sz_1663_, lean_object* v_i_1664_, lean_object* v_bs_1665_, lean_object* v___y_1666_){
_start:
{
size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1663_);
lean_dec(v_sz_1663_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(v_00_u03b1_1660_, v_00_u03b2_1661_, v_f_1662_, v_sz_boxed_1667_, v_i_boxed_1668_, v_bs_1665_, v___y_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_f_1672_, size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_bs_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1672_, v_sz_1673_, v_i_1674_, v_bs_1675_, v___y_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_f_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(v_00_u03b1_1678_, v_00_u03b2_1679_, v_f_1680_, v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1683_, v___y_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(lean_object* v_j_1701_, lean_object* v_k_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = l_Lean_Json_getObjValD(v_j_1701_, v_k_1702_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0___boxed(lean_object* v_j_1705_, lean_object* v_k_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_j_1705_, v_k_1706_);
lean_dec_ref(v_k_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0));
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_x_1710_);
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(lean_object* v_j_1714_, lean_object* v_k_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Lean_Json_getObjValD(v_j_1714_, v_k_1715_);
v___x_1717_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1___boxed(lean_object* v_j_1718_, lean_object* v_k_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_j_1718_, v_k_1719_);
lean_dec_ref(v_k_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(lean_object* v_json_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_a_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
v___x_1733_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1734_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1732_, v___x_1733_);
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1736_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1740_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1739_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1743_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1742_);
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1746_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1745_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1749_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1748_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1752_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1732_, v___x_1751_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1755_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1754_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1757_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_json_1732_);
v___x_1761_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1760_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1764_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1732_, v___x_1763_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1735_);
lean_ctor_set(v___x_1769_, 1, v_a_1738_);
lean_ctor_set(v___x_1769_, 2, v_a_1741_);
lean_ctor_set(v___x_1769_, 3, v_a_1744_);
lean_ctor_set(v___x_1769_, 4, v_a_1747_);
lean_ctor_set(v___x_1769_, 5, v_a_1750_);
lean_ctor_set(v___x_1769_, 6, v_a_1753_);
lean_ctor_set(v___x_1769_, 7, v_a_1756_);
lean_ctor_set(v___x_1769_, 8, v_a_1759_);
lean_ctor_set(v___x_1769_, 9, v_a_1762_);
lean_ctor_set(v___x_1769_, 10, v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1769_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(lean_object* v_k_1776_, lean_object* v_x_1777_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v_k_1776_);
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_val_1779_ = lean_ctor_get(v_x_1777_, 0);
lean_inc(v_val_1779_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_k_1776_);
lean_ctor_set(v___x_1780_, 1, v_val_1779_);
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0___boxed(lean_object* v_k_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v_k_1783_, v_x_1784_);
lean_dec(v_x_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__1(lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
if (lean_obj_tag(v_a_1786_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_array_to_list(v_a_1787_);
return v___x_1788_;
}
else
{
lean_object* v_head_1789_; lean_object* v_tail_1790_; lean_object* v___x_1791_; 
v_head_1789_ = lean_ctor_get(v_a_1786_, 0);
lean_inc(v_head_1789_);
v_tail_1790_ = lean_ctor_get(v_a_1786_, 1);
lean_inc(v_tail_1790_);
lean_dec_ref(v_a_1786_);
v___x_1791_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1787_, v_head_1789_);
v_a_1786_ = v_tail_1790_;
v_a_1787_ = v___x_1791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(lean_object* v_x_1795_){
_start:
{
lean_object* v_range_1796_; lean_object* v_fullRange_x3f_1797_; lean_object* v_severity_x3f_1798_; lean_object* v_isSilent_x3f_1799_; lean_object* v_code_x3f_1800_; lean_object* v_source_x3f_1801_; lean_object* v_message_1802_; lean_object* v_tags_x3f_1803_; lean_object* v_leanTags_x3f_1804_; lean_object* v_relatedInformation_x3f_1805_; lean_object* v_data_x3f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_range_1796_ = lean_ctor_get(v_x_1795_, 0);
v_fullRange_x3f_1797_ = lean_ctor_get(v_x_1795_, 1);
v_severity_x3f_1798_ = lean_ctor_get(v_x_1795_, 2);
v_isSilent_x3f_1799_ = lean_ctor_get(v_x_1795_, 3);
v_code_x3f_1800_ = lean_ctor_get(v_x_1795_, 4);
v_source_x3f_1801_ = lean_ctor_get(v_x_1795_, 5);
v_message_1802_ = lean_ctor_get(v_x_1795_, 6);
v_tags_x3f_1803_ = lean_ctor_get(v_x_1795_, 7);
v_leanTags_x3f_1804_ = lean_ctor_get(v_x_1795_, 8);
v_relatedInformation_x3f_1805_ = lean_ctor_get(v_x_1795_, 9);
v_data_x3f_1806_ = lean_ctor_get(v_x_1795_, 10);
v___x_1807_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_range_1796_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_range_1796_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1812_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1811_, v_fullRange_x3f_1797_);
v___x_1813_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1814_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1813_, v_severity_x3f_1798_);
v___x_1815_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1816_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1815_, v_isSilent_x3f_1799_);
v___x_1817_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1818_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1817_, v_code_x3f_1800_);
v___x_1819_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1820_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1819_, v_source_x3f_1801_);
v___x_1821_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_message_1802_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_message_1802_);
v___x_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1809_);
v___x_1824_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1825_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1824_, v_tags_x3f_1803_);
v___x_1826_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1827_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1826_, v_leanTags_x3f_1804_);
v___x_1828_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1829_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1828_, v_relatedInformation_x3f_1805_);
v___x_1830_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1831_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1830_, v_data_x3f_1806_);
v___x_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1809_);
v___x_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1829_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1827_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1825_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1823_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1820_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1818_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1816_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1814_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1812_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1810_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_));
v___x_1844_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__1(v___x_1842_, v___x_1843_);
v___x_1845_ = l_Lean_Json_mkObj(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57____boxed(lean_object* v_x_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(v_x_1846_);
lean_dec_ref(v_x_1846_);
return v_res_1847_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = l_Lean_JsonNumber_fromNat(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1853_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_unsigned_to_nat(2u);
v___x_1855_ = l_Lean_JsonNumber_fromNat(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1857_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1858_, lean_object* v___y_1859_){
_start:
{
if (v_a_1858_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___y_1859_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___y_1859_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v_a_boxed_1866_; lean_object* v_res_1867_; 
v_a_boxed_1866_ = lean_unbox(v_a_1864_);
v_res_1867_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1866_, v___y_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_a_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_a_1868_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1872_, lean_object* v___y_1873_){
_start:
{
if (v_a_1872_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___y_1873_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___y_1873_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v_a_boxed_1880_; lean_object* v_res_1881_; 
v_a_boxed_1880_ = lean_unbox(v_a_1878_);
v_res_1881_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1880_, v___y_1879_);
return v_res_1881_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(3u);
v___x_1932_ = l_Lean_JsonNumber_fromNat(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1934_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_unsigned_to_nat(4u);
v___x_1936_ = l_Lean_JsonNumber_fromNat(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1938_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_range_1942_; lean_object* v_fullRange_x3f_1943_; lean_object* v_severity_x3f_1944_; lean_object* v_isSilent_x3f_1945_; lean_object* v_code_x3f_1946_; lean_object* v_source_x3f_1947_; lean_object* v_message_1948_; lean_object* v_tags_x3f_1949_; lean_object* v_leanTags_x3f_1950_; lean_object* v_relatedInformation_x3f_1951_; lean_object* v_data_x3f_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2147_; 
v_range_1942_ = lean_ctor_get(v_a_1940_, 0);
v_fullRange_x3f_1943_ = lean_ctor_get(v_a_1940_, 1);
v_severity_x3f_1944_ = lean_ctor_get(v_a_1940_, 2);
v_isSilent_x3f_1945_ = lean_ctor_get(v_a_1940_, 3);
v_code_x3f_1946_ = lean_ctor_get(v_a_1940_, 4);
v_source_x3f_1947_ = lean_ctor_get(v_a_1940_, 5);
v_message_1948_ = lean_ctor_get(v_a_1940_, 6);
v_tags_x3f_1949_ = lean_ctor_get(v_a_1940_, 7);
v_leanTags_x3f_1950_ = lean_ctor_get(v_a_1940_, 8);
v_relatedInformation_x3f_1951_ = lean_ctor_get(v_a_1940_, 9);
v_data_x3f_1952_ = lean_ctor_get(v_a_1940_, 10);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_1940_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_1954_ = v_a_1940_;
v_isShared_1955_ = v_isSharedCheck_2147_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_data_x3f_1952_);
lean_inc(v_relatedInformation_x3f_1951_);
lean_inc(v_leanTags_x3f_1950_);
lean_inc(v_tags_x3f_1949_);
lean_inc(v_message_1948_);
lean_inc(v_source_x3f_1947_);
lean_inc(v_code_x3f_1946_);
lean_inc(v_isSilent_x3f_1945_);
lean_inc(v_severity_x3f_1944_);
lean_inc(v_fullRange_x3f_1943_);
lean_inc(v_range_1942_);
lean_dec(v_a_1940_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2147_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v_fst_2036_; lean_object* v_snd_2037_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v___y_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___y_2123_; lean_object* v_fst_2124_; lean_object* v_snd_2125_; lean_object* v_fst_2128_; lean_object* v_snd_2129_; 
v___f_1956_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1957_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1958_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_1959_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1942_);
if (lean_obj_tag(v_fullRange_x3f_1943_) == 0)
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_box(0);
v_fst_2128_ = v___x_2137_;
v_snd_2129_ = v_a_1941_;
goto v___jp_2127_;
}
else
{
lean_object* v_val_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_val_2138_ = lean_ctor_get(v_fullRange_x3f_1943_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_fullRange_x3f_1943_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v_fullRange_x3f_1943_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_val_2138_);
lean_dec(v_fullRange_x3f_1943_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_fst_2128_ = v___x_2144_;
v_snd_2129_ = v_a_1941_;
goto v___jp_2127_;
}
}
}
v___jp_1960_:
{
lean_object* v___x_1972_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 9, v_fst_1969_);
lean_ctor_set(v___x_1954_, 8, v___y_1966_);
lean_ctor_set(v___x_1954_, 7, v___y_1964_);
lean_ctor_set(v___x_1954_, 6, v___y_1968_);
lean_ctor_set(v___x_1954_, 5, v___y_1961_);
lean_ctor_set(v___x_1954_, 4, v___y_1965_);
lean_ctor_set(v___x_1954_, 3, v___y_1963_);
lean_ctor_set(v___x_1954_, 2, v___y_1967_);
lean_ctor_set(v___x_1954_, 1, v___y_1962_);
lean_ctor_set(v___x_1954_, 0, v___x_1959_);
v___x_1972_ = v___x_1954_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___y_1962_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v___y_1967_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v___y_1963_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v___y_1965_);
lean_ctor_set(v_reuseFailAlloc_1975_, 5, v___y_1961_);
lean_ctor_set(v_reuseFailAlloc_1975_, 6, v___y_1968_);
lean_ctor_set(v_reuseFailAlloc_1975_, 7, v___y_1964_);
lean_ctor_set(v_reuseFailAlloc_1975_, 8, v___y_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 9, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_1975_, 10, v_data_x3f_1952_);
v___x_1972_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(v___x_1972_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_snd_1970_);
return v___x_1974_;
}
}
v___jp_1976_:
{
lean_object* v___x_1986_; 
v___x_1986_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_relatedInformation_x3f_1951_) == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
v___y_1961_ = v___y_1978_;
v___y_1962_ = v___y_1977_;
v___y_1963_ = v___y_1979_;
v___y_1964_ = v___y_1980_;
v___y_1965_ = v___y_1981_;
v___y_1966_ = v_fst_1984_;
v___y_1967_ = v___y_1982_;
v___y_1968_ = v___y_1983_;
v_fst_1969_ = v___x_1987_;
v_snd_1970_ = v_snd_1985_;
goto v___jp_1960_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2003_; 
v_val_1988_ = lean_ctor_get(v_relatedInformation_x3f_1951_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_relatedInformation_x3f_1951_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1990_ = v_relatedInformation_x3f_1951_;
v_isShared_1991_ = v_isSharedCheck_2003_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v_relatedInformation_x3f_1951_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2003_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
size_t v_sz_1992_; size_t v___x_1993_; lean_object* v___x_7261__overap_1994_; lean_object* v___x_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_sz_1992_ = lean_array_size(v_val_1988_);
v___x_1993_ = ((size_t)0ULL);
v___x_7261__overap_1994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1986_, v___f_1957_, v_sz_1992_, v___x_1993_, v_val_1988_);
v___x_1995_ = lean_apply_1(v___x_7261__overap_1994_, v_snd_1985_);
v_fst_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_fst_1996_);
v_snd_1997_ = lean_ctor_get(v___x_1995_, 1);
lean_inc(v_snd_1997_);
lean_dec_ref(v___x_1995_);
v___x_1998_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_1999_ = l_Array_toJson___redArg(v___x_1998_, v_fst_1996_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1999_);
v___x_2001_ = v___x_1990_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
v___y_1961_ = v___y_1978_;
v___y_1962_ = v___y_1977_;
v___y_1963_ = v___y_1979_;
v___y_1964_ = v___y_1980_;
v___y_1965_ = v___y_1981_;
v___y_1966_ = v_fst_1984_;
v___y_1967_ = v___y_1982_;
v___y_1968_ = v___y_1983_;
v_fst_1969_ = v___x_2001_;
v_snd_1970_ = v_snd_1997_;
goto v___jp_1960_;
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2013_; 
v___x_2013_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_leanTags_x3f_1950_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_box(0);
v___y_1977_ = v___y_2006_;
v___y_1978_ = v___y_2005_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v_fst_2011_;
v___y_1981_ = v___y_2008_;
v___y_1982_ = v___y_2009_;
v___y_1983_ = v___y_2010_;
v_fst_1984_ = v___x_2014_;
v_snd_1985_ = v_snd_2012_;
goto v___jp_1976_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2030_; 
v_val_2015_ = lean_ctor_get(v_leanTags_x3f_1950_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_leanTags_x3f_1950_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2017_ = v_leanTags_x3f_1950_;
v_isShared_2018_ = v_isSharedCheck_2030_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v_leanTags_x3f_1950_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2030_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
size_t v_sz_2019_; size_t v___x_2020_; lean_object* v___x_7285__overap_2021_; lean_object* v___x_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v_sz_2019_ = lean_array_size(v_val_2015_);
v___x_2020_ = ((size_t)0ULL);
v___x_7285__overap_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2013_, v___f_1956_, v_sz_2019_, v___x_2020_, v_val_2015_);
v___x_2022_ = lean_apply_1(v___x_7285__overap_2021_, v_snd_2012_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_fst_2023_);
v_snd_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2022_);
v___x_2025_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2026_ = l_Array_toJson___redArg(v___x_2025_, v_fst_2023_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2026_);
v___x_2028_ = v___x_2017_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v___y_1977_ = v___y_2006_;
v___y_1978_ = v___y_2005_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v_fst_2011_;
v___y_1981_ = v___y_2008_;
v___y_1982_ = v___y_2009_;
v___y_1983_ = v___y_2010_;
v_fst_1984_ = v___x_2028_;
v_snd_1985_ = v_snd_2024_;
goto v___jp_1976_;
}
}
}
}
v___jp_2031_:
{
lean_object* v_rpcEncode_2038_; lean_object* v___x_2039_; lean_object* v_fst_2040_; lean_object* v_snd_2041_; lean_object* v___x_2042_; 
v_rpcEncode_2038_ = lean_ctor_get(v_inst_1939_, 0);
lean_inc_ref(v_rpcEncode_2038_);
lean_dec_ref(v_inst_1939_);
v___x_2039_ = lean_apply_2(v_rpcEncode_2038_, v_message_1948_, v_snd_2037_);
v_fst_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_fst_2040_);
v_snd_2041_ = lean_ctor_get(v___x_2039_, 1);
lean_inc(v_snd_2041_);
lean_dec_ref(v___x_2039_);
v___x_2042_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_tags_x3f_1949_) == 0)
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_box(0);
v___y_2005_ = v_fst_2036_;
v___y_2006_ = v___y_2032_;
v___y_2007_ = v___y_2033_;
v___y_2008_ = v___y_2034_;
v___y_2009_ = v___y_2035_;
v___y_2010_ = v_fst_2040_;
v_fst_2011_ = v___x_2043_;
v_snd_2012_ = v_snd_2041_;
goto v___jp_2004_;
}
else
{
lean_object* v_val_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2059_; 
v_val_2044_ = lean_ctor_get(v_tags_x3f_1949_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_tags_x3f_1949_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2046_ = v_tags_x3f_1949_;
v_isShared_2047_ = v_isSharedCheck_2059_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_val_2044_);
lean_dec(v_tags_x3f_1949_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2059_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
size_t v_sz_2048_; size_t v___x_2049_; lean_object* v___x_7309__overap_2050_; lean_object* v___x_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v_sz_2048_ = lean_array_size(v_val_2044_);
v___x_2049_ = ((size_t)0ULL);
v___x_7309__overap_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2042_, v___f_1958_, v_sz_2048_, v___x_2049_, v_val_2044_);
v___x_2051_ = lean_apply_1(v___x_7309__overap_2050_, v_snd_2041_);
v_fst_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_fst_2052_);
v_snd_2053_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2051_);
v___x_2054_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2055_ = l_Array_toJson___redArg(v___x_2054_, v_fst_2052_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2055_);
v___x_2057_ = v___x_2046_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
v___y_2005_ = v_fst_2036_;
v___y_2006_ = v___y_2032_;
v___y_2007_ = v___y_2033_;
v___y_2008_ = v___y_2034_;
v___y_2009_ = v___y_2035_;
v___y_2010_ = v_fst_2040_;
v_fst_2011_ = v___x_2057_;
v_snd_2012_ = v_snd_2053_;
goto v___jp_2004_;
}
}
}
}
v___jp_2060_:
{
if (lean_obj_tag(v_source_x3f_1947_) == 0)
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_box(0);
v___y_2032_ = v___y_2061_;
v___y_2033_ = v___y_2062_;
v___y_2034_ = v_fst_2064_;
v___y_2035_ = v___y_2063_;
v_fst_2036_ = v___x_2066_;
v_snd_2037_ = v_snd_2065_;
goto v___jp_2031_;
}
else
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_val_2067_ = lean_ctor_get(v_source_x3f_1947_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_source_x3f_1947_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v_source_x3f_1947_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v_source_x3f_1947_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_val_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
v___y_2032_ = v___y_2061_;
v___y_2033_ = v___y_2062_;
v___y_2034_ = v_fst_2064_;
v___y_2035_ = v___y_2063_;
v_fst_2036_ = v___x_2073_;
v_snd_2037_ = v_snd_2065_;
goto v___jp_2031_;
}
}
}
}
v___jp_2076_:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_fst_2080_);
v___y_2061_ = v___y_2077_;
v___y_2062_ = v___y_2078_;
v___y_2063_ = v___y_2079_;
v_fst_2064_ = v___x_2082_;
v_snd_2065_ = v_snd_2081_;
goto v___jp_2060_;
}
v___jp_2083_:
{
if (lean_obj_tag(v_code_x3f_1946_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_box(0);
v___y_2061_ = v___y_2084_;
v___y_2062_ = v_fst_2086_;
v___y_2063_ = v___y_2085_;
v_fst_2064_ = v___x_2088_;
v_snd_2065_ = v_snd_2087_;
goto v___jp_2060_;
}
else
{
lean_object* v_val_2089_; 
v_val_2089_ = lean_ctor_get(v_code_x3f_1946_, 0);
lean_inc(v_val_2089_);
lean_dec_ref(v_code_x3f_1946_);
if (lean_obj_tag(v_val_2089_) == 0)
{
lean_object* v_i_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_i_2090_ = lean_ctor_get(v_val_2089_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_val_2089_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2092_ = v_val_2089_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_i_2090_);
lean_dec(v_val_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = l_Lean_JsonNumber_fromInt(v_i_2090_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 2);
lean_ctor_set(v___x_2092_, 0, v___x_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v___y_2077_ = v___y_2084_;
v___y_2078_ = v_fst_2086_;
v___y_2079_ = v___y_2085_;
v_fst_2080_ = v___x_2096_;
v_snd_2081_ = v_snd_2087_;
goto v___jp_2076_;
}
}
}
else
{
lean_object* v_s_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_s_2099_ = lean_ctor_get(v_val_2089_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_val_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v_val_2089_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_s_2099_);
lean_dec(v_val_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 3);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_s_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v___y_2077_ = v___y_2084_;
v___y_2078_ = v_fst_2086_;
v___y_2079_ = v___y_2085_;
v_fst_2080_ = v___x_2104_;
v_snd_2081_ = v_snd_2087_;
goto v___jp_2076_;
}
}
}
}
}
v___jp_2107_:
{
if (lean_obj_tag(v_isSilent_x3f_1945_) == 0)
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_box(0);
v___y_2084_ = v___y_2108_;
v___y_2085_ = v_fst_2109_;
v_fst_2086_ = v___x_2111_;
v_snd_2087_ = v_snd_2110_;
goto v___jp_2083_;
}
else
{
lean_object* v_val_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2121_; 
v_val_2112_ = lean_ctor_get(v_isSilent_x3f_1945_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_isSilent_x3f_1945_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2114_ = v_isSilent_x3f_1945_;
v_isShared_2115_ = v_isSharedCheck_2121_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_val_2112_);
lean_dec(v_isSilent_x3f_1945_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2121_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2119_; 
v___x_2116_ = lean_alloc_ctor(1, 0, 1);
v___x_2117_ = lean_unbox(v_val_2112_);
lean_dec(v_val_2112_);
lean_ctor_set_uint8(v___x_2116_, 0, v___x_2117_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2116_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2116_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
v___y_2084_ = v___y_2108_;
v___y_2085_ = v_fst_2109_;
v_fst_2086_ = v___x_2119_;
v_snd_2087_ = v_snd_2110_;
goto v___jp_2083_;
}
}
}
}
v___jp_2122_:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_fst_2124_);
v___y_2108_ = v___y_2123_;
v_fst_2109_ = v___x_2126_;
v_snd_2110_ = v_snd_2125_;
goto v___jp_2107_;
}
v___jp_2127_:
{
if (lean_obj_tag(v_severity_x3f_1944_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_box(0);
v___y_2108_ = v_fst_2128_;
v_fst_2109_ = v___x_2130_;
v_snd_2110_ = v_snd_2129_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2131_; uint8_t v___x_2132_; 
v_val_2131_ = lean_ctor_get(v_severity_x3f_1944_, 0);
lean_inc(v_val_2131_);
lean_dec_ref(v_severity_x3f_1944_);
v___x_2132_ = lean_unbox(v_val_2131_);
lean_dec(v_val_2131_);
switch(v___x_2132_)
{
case 0:
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2123_ = v_fst_2128_;
v_fst_2124_ = v___x_2133_;
v_snd_2125_ = v_snd_2129_;
goto v___jp_2122_;
}
case 1:
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2123_ = v_fst_2128_;
v_fst_2124_ = v___x_2134_;
v_snd_2125_ = v_snd_2129_;
goto v___jp_2122_;
}
case 2:
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2123_ = v_fst_2128_;
v_fst_2124_ = v___x_2135_;
v_snd_2125_ = v_snd_2129_;
goto v___jp_2122_;
}
default: 
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2123_ = v_fst_2128_;
v_fst_2124_ = v___x_2136_;
v_snd_2125_ = v_snd_2129_;
goto v___jp_2122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2148_, lean_object* v_inst_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2149_, v_a_2150_, v_a_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v_j_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_10281__overap_2158_; lean_object* v___x_2159_; 
v___x_2157_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_j_2155_);
v___x_10281__overap_2158_ = l_MonadExcept_ofExcept___redArg(v___x_2153_, v___x_2154_, v___x_2157_);
v___x_2159_ = lean_apply_1(v___x_10281__overap_2158_, v___y_2156_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2169_, lean_object* v___x_2170_, lean_object* v_j_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Json_getNat_x3f(v_j_2171_);
if (lean_obj_tag(v___x_2177_) == 1)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_dec_eq(v_a_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(2u);
v___x_2182_ = lean_nat_dec_eq(v_a_2178_, v___x_2181_);
lean_dec(v_a_2178_);
if (v___x_2182_ == 0)
{
goto v___jp_2173_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_10297__overap_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10297__overap_2184_ = l_MonadExcept_ofExcept___redArg(v___x_2169_, v___x_2170_, v___x_2183_);
v___x_2185_ = lean_apply_1(v___x_10297__overap_2184_, v___y_2172_);
return v___x_2185_;
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_10300__overap_2187_; lean_object* v___x_2188_; 
lean_dec(v_a_2178_);
v___x_2186_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10300__overap_2187_ = l_MonadExcept_ofExcept___redArg(v___x_2169_, v___x_2170_, v___x_2186_);
v___x_2188_ = lean_apply_1(v___x_10300__overap_2187_, v___y_2172_);
return v___x_2188_;
}
}
else
{
lean_dec_ref(v___x_2177_);
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2174_; lean_object* v___x_10288__overap_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10288__overap_2175_ = l_MonadExcept_ofExcept___redArg(v___x_2169_, v___x_2170_, v___x_2174_);
v___x_2176_ = lean_apply_1(v___x_10288__overap_2175_, v___y_2172_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v_j_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Json_getNat_x3f(v_j_2200_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_dec_eq(v_a_2207_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = lean_unsigned_to_nat(2u);
v___x_2211_ = lean_nat_dec_eq(v_a_2207_, v___x_2210_);
lean_dec(v_a_2207_);
if (v___x_2211_ == 0)
{
goto v___jp_2202_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_10316__overap_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10316__overap_2213_ = l_MonadExcept_ofExcept___redArg(v___x_2198_, v___x_2199_, v___x_2212_);
v___x_2214_ = lean_apply_1(v___x_10316__overap_2213_, v___y_2201_);
return v___x_2214_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_10319__overap_2216_; lean_object* v___x_2217_; 
lean_dec(v_a_2207_);
v___x_2215_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10319__overap_2216_ = l_MonadExcept_ofExcept___redArg(v___x_2198_, v___x_2199_, v___x_2215_);
v___x_2217_ = lean_apply_1(v___x_10319__overap_2216_, v___y_2201_);
return v___x_2217_;
}
}
else
{
lean_dec_ref(v___x_2206_);
goto v___jp_2202_;
}
v___jp_2202_:
{
lean_object* v___x_2203_; lean_object* v___x_10307__overap_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10307__overap_2204_ = l_MonadExcept_ofExcept___redArg(v___x_2198_, v___x_2199_, v___x_2203_);
v___x_2205_ = lean_apply_1(v___x_10307__overap_2204_, v___y_2201_);
return v___x_2205_;
}
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2219_ = l_ReaderT_instMonad___redArg(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___f_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2221_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2221_, 0, v___x_2220_);
return v___f_2221_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___f_2223_; 
v___x_2222_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2223_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_2223_, 0, v___x_2222_);
return v___f_2223_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___f_2225_; 
v___x_2224_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2225_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_2225_, 0, v___x_2224_);
return v___f_2225_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___f_2227_; 
v___x_2226_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2227_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_2227_, 0, v___x_2226_);
return v___f_2227_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2229_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_2229_, 0, lean_box(0));
lean_closure_set(v___x_2229_, 1, lean_box(0));
lean_closure_set(v___x_2229_, 2, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___f_2230_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2231_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___f_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2234_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_2234_, 0, lean_box(0));
lean_closure_set(v___x_2234_, 1, lean_box(0));
lean_closure_set(v___x_2234_, 2, v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2235_; lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___f_2235_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2236_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2237_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2238_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2239_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set(v___x_2240_, 2, v___f_2237_);
lean_ctor_set(v___x_2240_, 3, v___f_2236_);
lean_ctor_set(v___x_2240_, 4, v___f_2235_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2242_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_2242_, 0, lean_box(0));
lean_closure_set(v___x_2242_, 1, lean_box(0));
lean_closure_set(v___x_2242_, 2, v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2244_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2247_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_2247_, 0, lean_box(0));
lean_closure_set(v___x_2247_, 1, lean_box(0));
lean_closure_set(v___x_2247_, 2, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_2263_, lean_object* v_j_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(v_j_2264_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_inst_2263_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2715_; 
v_a_2275_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2277_ = v___x_2266_;
v_isShared_2278_ = v_isSharedCheck_2715_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2266_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2715_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_toApplicative_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2713_; 
v___x_2279_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2280_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v_toApplicative_2281_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; 
v_unused_2714_ = lean_ctor_get(v___x_2279_, 1);
lean_dec(v_unused_2714_);
v___x_2283_ = v___x_2279_;
v_isShared_2284_ = v_isSharedCheck_2713_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_toApplicative_2281_);
lean_dec(v___x_2279_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2713_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_toPure_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v_toPure_2285_ = lean_ctor_get(v_toApplicative_2281_, 1);
lean_inc(v_toPure_2285_);
lean_dec_ref(v_toApplicative_2281_);
v___f_2286_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2286_, 0, v_toPure_2285_);
v___x_2287_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v___x_2287_);
lean_ctor_set(v___x_2283_, 0, v___f_2286_);
v___x_2289_ = v___x_2283_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___f_2286_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; lean_object* v_range_2291_; lean_object* v_fullRange_x3f_2292_; lean_object* v_severity_x3f_2293_; lean_object* v_isSilent_x3f_2294_; lean_object* v_code_x3f_2295_; lean_object* v_source_x3f_2296_; lean_object* v_message_2297_; lean_object* v_tags_x3f_2298_; lean_object* v_leanTags_x3f_2299_; lean_object* v_relatedInformation_x3f_2300_; lean_object* v_data_x3f_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2711_; 
v___x_2290_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2289_);
v_range_2291_ = lean_ctor_get(v_a_2275_, 0);
v_fullRange_x3f_2292_ = lean_ctor_get(v_a_2275_, 1);
v_severity_x3f_2293_ = lean_ctor_get(v_a_2275_, 2);
v_isSilent_x3f_2294_ = lean_ctor_get(v_a_2275_, 3);
v_code_x3f_2295_ = lean_ctor_get(v_a_2275_, 4);
v_source_x3f_2296_ = lean_ctor_get(v_a_2275_, 5);
v_message_2297_ = lean_ctor_get(v_a_2275_, 6);
v_tags_x3f_2298_ = lean_ctor_get(v_a_2275_, 7);
v_leanTags_x3f_2299_ = lean_ctor_get(v_a_2275_, 8);
v_relatedInformation_x3f_2300_ = lean_ctor_get(v_a_2275_, 9);
v_data_x3f_2301_ = lean_ctor_get(v_a_2275_, 10);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2303_ = v_a_2275_;
v_isShared_2304_ = v_isSharedCheck_2711_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_data_x3f_2301_);
lean_inc(v_relatedInformation_x3f_2300_);
lean_inc(v_leanTags_x3f_2299_);
lean_inc(v_tags_x3f_2298_);
lean_inc(v_message_2297_);
lean_inc(v_source_x3f_2296_);
lean_inc(v_code_x3f_2295_);
lean_inc(v_isSilent_x3f_2294_);
lean_inc(v_severity_x3f_2293_);
lean_inc(v_fullRange_x3f_2292_);
lean_inc(v_range_2291_);
lean_dec(v_a_2275_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2711_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_9532__overap_2306_; lean_object* v___x_2307_; 
v___x_2305_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_range_2291_);
lean_inc_ref(v___x_2290_);
v___x_9532__overap_2306_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2305_);
lean_inc_ref(v_a_2265_);
v___x_2307_ = lean_apply_1(v___x_9532__overap_2306_, v_a_2265_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec(v_source_x3f_2296_);
lean_dec(v_code_x3f_2295_);
lean_dec(v_isSilent_x3f_2294_);
lean_dec(v_severity_x3f_2293_);
lean_dec(v_fullRange_x3f_2292_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_inst_2263_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2710_; 
v_a_2316_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2318_ = v___x_2307_;
v_isShared_2319_ = v_isSharedCheck_2710_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2307_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2710_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v_____do__lift_2330_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v_____do__lift_2346_; lean_object* v___y_2347_; lean_object* v___f_2370_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v_____do__lift_2379_; lean_object* v___y_2380_; lean_object* v___f_2414_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v_____do__lift_2422_; lean_object* v___y_2423_; lean_object* v___f_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_____do__lift_2463_; lean_object* v___y_2464_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v_____do__lift_2514_; lean_object* v___y_2515_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v_j_2558_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v_____do__lift_2571_; lean_object* v___y_2572_; lean_object* v___y_2611_; lean_object* v_____do__lift_2612_; lean_object* v___y_2613_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v_____do__lift_2663_; lean_object* v___y_2664_; 
lean_inc_ref(v___x_2290_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___f_2370_, 0, v___x_2280_);
lean_closure_set(v___f_2370_, 1, v___x_2290_);
lean_inc_ref(v___x_2290_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___f_2414_, 0, v___x_2280_);
lean_closure_set(v___f_2414_, 1, v___x_2290_);
lean_inc_ref(v___x_2290_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___f_2457_, 0, v___x_2280_);
lean_closure_set(v___f_2457_, 1, v___x_2290_);
if (lean_obj_tag(v_fullRange_x3f_2292_) == 0)
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_box(0);
v_____do__lift_2663_ = v___x_2689_;
v___y_2664_ = v_a_2265_;
goto v___jp_2662_;
}
else
{
lean_object* v_val_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2709_; 
v_val_2690_ = lean_ctor_get(v_fullRange_x3f_2292_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_fullRange_x3f_2292_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2692_ = v_fullRange_x3f_2292_;
v_isShared_2693_ = v_isSharedCheck_2709_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_val_2690_);
lean_dec(v_fullRange_x3f_2292_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2709_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_9910__overap_2695_; lean_object* v___x_2696_; 
v___x_2694_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_2690_);
lean_inc_ref(v___x_2290_);
v___x_9910__overap_2695_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2694_);
lean_inc_ref(v_a_2265_);
v___x_2696_ = lean_apply_1(v___x_9910__overap_2695_, v_a_2265_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_del_object(v___x_2692_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec(v_source_x3f_2296_);
lean_dec(v_code_x3f_2295_);
lean_dec(v_isSilent_x3f_2294_);
lean_dec(v_severity_x3f_2293_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_inst_2263_);
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; 
v_a_2705_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2696_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_a_2705_);
v___x_2707_ = v___x_2692_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
v_____do__lift_2663_ = v___x_2707_;
v___y_2664_ = v_a_2265_;
goto v___jp_2662_;
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2332_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 10, v_____do__lift_2330_);
lean_ctor_set(v___x_2303_, 9, v___y_2324_);
lean_ctor_set(v___x_2303_, 8, v___y_2325_);
lean_ctor_set(v___x_2303_, 7, v___y_2321_);
lean_ctor_set(v___x_2303_, 6, v___y_2322_);
lean_ctor_set(v___x_2303_, 5, v___y_2327_);
lean_ctor_set(v___x_2303_, 4, v___y_2323_);
lean_ctor_set(v___x_2303_, 3, v___y_2326_);
lean_ctor_set(v___x_2303_, 2, v___y_2328_);
lean_ctor_set(v___x_2303_, 1, v___y_2329_);
lean_ctor_set(v___x_2303_, 0, v_a_2316_);
v___x_2332_ = v___x_2303_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2316_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___y_2329_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v___y_2328_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v___y_2326_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v___y_2323_);
lean_ctor_set(v_reuseFailAlloc_2336_, 5, v___y_2327_);
lean_ctor_set(v_reuseFailAlloc_2336_, 6, v___y_2322_);
lean_ctor_set(v_reuseFailAlloc_2336_, 7, v___y_2321_);
lean_ctor_set(v_reuseFailAlloc_2336_, 8, v___y_2325_);
lean_ctor_set(v_reuseFailAlloc_2336_, 9, v___y_2324_);
lean_ctor_set(v_reuseFailAlloc_2336_, 10, v_____do__lift_2330_);
v___x_2332_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2332_);
v___x_2334_ = v___x_2318_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
v___jp_2337_:
{
if (lean_obj_tag(v_data_x3f_2301_) == 0)
{
lean_dec_ref(v___y_2347_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v___y_2321_ = v___y_2339_;
v___y_2322_ = v___y_2338_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v_____do__lift_2346_;
v___y_2325_ = v___y_2342_;
v___y_2326_ = v___y_2341_;
v___y_2327_ = v___y_2344_;
v___y_2328_ = v___y_2343_;
v___y_2329_ = v___y_2345_;
v_____do__lift_2330_ = v_data_x3f_2301_;
goto v___jp_2320_;
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2369_; 
v_val_2348_ = lean_ctor_get(v_data_x3f_2301_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_data_x3f_2301_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2350_ = v_data_x3f_2301_;
v_isShared_2351_ = v_isSharedCheck_2369_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_val_2348_);
lean_dec(v_data_x3f_2301_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2369_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_val_2348_);
v___x_2353_ = v___x_2277_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_val_2348_);
v___x_2353_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_9964__overap_2354_; lean_object* v___x_2355_; 
v___x_9964__overap_2354_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2353_);
v___x_2355_ = lean_apply_1(v___x_9964__overap_2354_, v___y_2347_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2350_);
lean_dec(v_____do__lift_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2355_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_a_2364_);
v___x_2366_ = v___x_2350_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
v___y_2321_ = v___y_2339_;
v___y_2322_ = v___y_2338_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v_____do__lift_2346_;
v___y_2325_ = v___y_2342_;
v___y_2326_ = v___y_2341_;
v___y_2327_ = v___y_2344_;
v___y_2328_ = v___y_2343_;
v___y_2329_ = v___y_2345_;
v_____do__lift_2330_ = v___x_2366_;
goto v___jp_2320_;
}
}
}
}
}
}
v___jp_2371_:
{
if (lean_obj_tag(v_relatedInformation_x3f_2300_) == 0)
{
lean_object* v___x_2381_; 
lean_dec_ref(v___f_2370_);
v___x_2381_ = lean_box(0);
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2372_;
v___y_2340_ = v___y_2374_;
v___y_2341_ = v___y_2375_;
v___y_2342_ = v_____do__lift_2379_;
v___y_2343_ = v___y_2377_;
v___y_2344_ = v___y_2376_;
v___y_2345_ = v___y_2378_;
v_____do__lift_2346_ = v___x_2381_;
v___y_2347_ = v___y_2380_;
goto v___jp_2337_;
}
else
{
lean_object* v_val_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2413_; 
v_val_2382_ = lean_ctor_get(v_relatedInformation_x3f_2300_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_relatedInformation_x3f_2300_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2384_ = v_relatedInformation_x3f_2300_;
v_isShared_2385_ = v_isSharedCheck_2413_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_val_2382_);
lean_dec(v_relatedInformation_x3f_2300_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2413_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___f_2386_; lean_object* v___x_2387_; 
v___f_2386_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2387_ = l_Array_fromJson_x3f___redArg(v___f_2386_, v_val_2382_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_del_object(v___x_2384_);
lean_dec_ref(v___y_2380_);
lean_dec(v_____do__lift_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_object* v_a_2396_; size_t v_sz_2397_; size_t v___x_2398_; lean_object* v___x_10014__overap_2399_; lean_object* v___x_2400_; 
v_a_2396_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2387_);
v_sz_2397_ = lean_array_size(v_a_2396_);
v___x_2398_ = ((size_t)0ULL);
v___x_10014__overap_2399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2280_, v___f_2370_, v_sz_2397_, v___x_2398_, v_a_2396_);
lean_inc_ref(v___y_2380_);
v___x_2400_ = lean_apply_1(v___x_10014__overap_2399_, v___y_2380_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_del_object(v___x_2384_);
lean_dec_ref(v___y_2380_);
lean_dec(v_____do__lift_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2409_);
lean_dec_ref(v___x_2400_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_a_2409_);
v___x_2411_ = v___x_2384_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2372_;
v___y_2340_ = v___y_2374_;
v___y_2341_ = v___y_2375_;
v___y_2342_ = v_____do__lift_2379_;
v___y_2343_ = v___y_2377_;
v___y_2344_ = v___y_2376_;
v___y_2345_ = v___y_2378_;
v_____do__lift_2346_ = v___x_2411_;
v___y_2347_ = v___y_2380_;
goto v___jp_2337_;
}
}
}
}
}
}
v___jp_2415_:
{
if (lean_obj_tag(v_leanTags_x3f_2299_) == 0)
{
lean_object* v___x_2424_; 
lean_dec_ref(v___f_2414_);
v___x_2424_ = lean_box(0);
v___y_2372_ = v_____do__lift_2422_;
v___y_2373_ = v___y_2416_;
v___y_2374_ = v___y_2417_;
v___y_2375_ = v___y_2418_;
v___y_2376_ = v___y_2420_;
v___y_2377_ = v___y_2419_;
v___y_2378_ = v___y_2421_;
v_____do__lift_2379_ = v___x_2424_;
v___y_2380_ = v___y_2423_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2456_; 
v_val_2425_ = lean_ctor_get(v_leanTags_x3f_2299_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_leanTags_x3f_2299_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2427_ = v_leanTags_x3f_2299_;
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v_leanTags_x3f_2299_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___f_2429_; lean_object* v___x_2430_; 
v___f_2429_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2430_ = l_Array_fromJson_x3f___redArg(v___f_2429_, v_val_2425_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2427_);
lean_dec_ref(v___y_2423_);
lean_dec(v_____do__lift_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
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
lean_object* v_a_2439_; size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_10063__overap_2442_; lean_object* v___x_2443_; 
v_a_2439_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2430_);
v_sz_2440_ = lean_array_size(v_a_2439_);
v___x_2441_ = ((size_t)0ULL);
v___x_10063__overap_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2280_, v___f_2414_, v_sz_2440_, v___x_2441_, v_a_2439_);
lean_inc_ref(v___y_2423_);
v___x_2443_ = lean_apply_1(v___x_10063__overap_2442_, v___y_2423_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_del_object(v___x_2427_);
lean_dec_ref(v___y_2423_);
lean_dec(v_____do__lift_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
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
lean_dec_ref(v___x_2443_);
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
v___y_2372_ = v_____do__lift_2422_;
v___y_2373_ = v___y_2416_;
v___y_2374_ = v___y_2417_;
v___y_2375_ = v___y_2418_;
v___y_2376_ = v___y_2420_;
v___y_2377_ = v___y_2419_;
v___y_2378_ = v___y_2421_;
v_____do__lift_2379_ = v___x_2454_;
v___y_2380_ = v___y_2423_;
goto v___jp_2371_;
}
}
}
}
}
}
v___jp_2458_:
{
lean_object* v_rpcDecode_2465_; lean_object* v___x_2466_; 
v_rpcDecode_2465_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc_ref(v_rpcDecode_2465_);
lean_dec_ref(v_inst_2263_);
lean_inc_ref(v___y_2464_);
v___x_2466_ = lean_apply_2(v_rpcDecode_2465_, v_message_2297_, v___y_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v___y_2464_);
lean_dec(v_____do__lift_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
if (lean_obj_tag(v_tags_x3f_2298_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
lean_dec_ref(v___f_2457_);
v_a_2475_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2466_);
v___x_2476_ = lean_box(0);
v___y_2416_ = v_a_2475_;
v___y_2417_ = v___y_2459_;
v___y_2418_ = v___y_2460_;
v___y_2419_ = v___y_2461_;
v___y_2420_ = v_____do__lift_2463_;
v___y_2421_ = v___y_2462_;
v_____do__lift_2422_ = v___x_2476_;
v___y_2423_ = v___y_2464_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2477_; lean_object* v_val_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2509_; 
v_a_2477_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2466_);
v_val_2478_ = lean_ctor_get(v_tags_x3f_2298_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_tags_x3f_2298_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2480_ = v_tags_x3f_2298_;
v_isShared_2481_ = v_isSharedCheck_2509_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_val_2478_);
lean_dec(v_tags_x3f_2298_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2509_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___f_2482_; lean_object* v___x_2483_; 
v___f_2482_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2483_ = l_Array_fromJson_x3f___redArg(v___f_2482_, v_val_2478_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_del_object(v___x_2480_);
lean_dec(v_a_2477_);
lean_dec_ref(v___y_2464_);
lean_dec(v_____do__lift_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_object* v_a_2492_; size_t v_sz_2493_; size_t v___x_2494_; lean_object* v___x_10112__overap_2495_; lean_object* v___x_2496_; 
v_a_2492_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2492_);
lean_dec_ref(v___x_2483_);
v_sz_2493_ = lean_array_size(v_a_2492_);
v___x_2494_ = ((size_t)0ULL);
v___x_10112__overap_2495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2280_, v___f_2457_, v_sz_2493_, v___x_2494_, v_a_2492_);
lean_inc_ref(v___y_2464_);
v___x_2496_ = lean_apply_1(v___x_10112__overap_2495_, v___y_2464_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2480_);
lean_dec(v_a_2477_);
lean_dec_ref(v___y_2464_);
lean_dec(v_____do__lift_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2496_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2505_);
v___x_2507_ = v___x_2480_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v___y_2416_ = v_a_2477_;
v___y_2417_ = v___y_2459_;
v___y_2418_ = v___y_2460_;
v___y_2419_ = v___y_2461_;
v___y_2420_ = v_____do__lift_2463_;
v___y_2421_ = v___y_2462_;
v_____do__lift_2422_ = v___x_2507_;
v___y_2423_ = v___y_2464_;
goto v___jp_2415_;
}
}
}
}
}
}
}
v___jp_2510_:
{
if (lean_obj_tag(v_source_x3f_2296_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_box(0);
v___y_2459_ = v_____do__lift_2514_;
v___y_2460_ = v___y_2511_;
v___y_2461_ = v___y_2512_;
v___y_2462_ = v___y_2513_;
v_____do__lift_2463_ = v___x_2516_;
v___y_2464_ = v___y_2515_;
goto v___jp_2458_;
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2536_; 
v_val_2517_ = lean_ctor_get(v_source_x3f_2296_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_source_x3f_2296_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2519_ = v_source_x3f_2296_;
v_isShared_2520_ = v_isSharedCheck_2536_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v_source_x3f_2296_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2536_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_9778__overap_2522_; lean_object* v___x_2523_; 
v___x_2521_ = l_Lean_Json_getStr_x3f(v_val_2517_);
lean_inc_ref(v___x_2290_);
v___x_9778__overap_2522_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2521_);
lean_inc_ref(v___y_2515_);
v___x_2523_ = lean_apply_1(v___x_9778__overap_2522_, v___y_2515_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_del_object(v___x_2519_);
lean_dec_ref(v___y_2515_);
lean_dec(v_____do__lift_2514_);
lean_dec(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_inst_2263_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; 
v_a_2532_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2523_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v_a_2532_);
v___x_2534_ = v___x_2519_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
v___y_2459_ = v_____do__lift_2514_;
v___y_2460_ = v___y_2511_;
v___y_2461_ = v___y_2512_;
v___y_2462_ = v___y_2513_;
v_____do__lift_2463_ = v___x_2534_;
v___y_2464_ = v___y_2515_;
goto v___jp_2458_;
}
}
}
}
}
v___jp_2537_:
{
if (lean_obj_tag(v___y_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec(v_source_x3f_2296_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_inst_2263_);
v_a_2543_ = lean_ctor_get(v___y_2542_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___y_2542_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___y_2542_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___y_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___y_2542_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___y_2542_);
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_a_2551_);
v___y_2511_ = v___y_2539_;
v___y_2512_ = v___y_2540_;
v___y_2513_ = v___y_2541_;
v_____do__lift_2514_ = v___x_2552_;
v___y_2515_ = v___y_2538_;
goto v___jp_2510_;
}
}
v___jp_2553_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_9822__overap_2566_; lean_object* v___x_2567_; 
v___x_2559_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2560_ = lean_unsigned_to_nat(80u);
v___x_2561_ = l_Lean_Json_pretty(v_j_2558_, v___x_2560_);
v___x_2562_ = lean_string_append(v___x_2559_, v___x_2561_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2564_ = lean_string_append(v___x_2562_, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_inc_ref(v___x_2290_);
v___x_9822__overap_2566_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2565_);
lean_inc_ref(v___y_2554_);
v___x_2567_ = lean_apply_1(v___x_9822__overap_2566_, v___y_2554_);
v___y_2538_ = v___y_2554_;
v___y_2539_ = v___y_2555_;
v___y_2540_ = v___y_2556_;
v___y_2541_ = v___y_2557_;
v___y_2542_ = v___x_2567_;
goto v___jp_2537_;
}
v___jp_2568_:
{
if (lean_obj_tag(v_code_x3f_2295_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_box(0);
v___y_2511_ = v_____do__lift_2571_;
v___y_2512_ = v___y_2569_;
v___y_2513_ = v___y_2570_;
v_____do__lift_2514_ = v___x_2573_;
v___y_2515_ = v___y_2572_;
goto v___jp_2510_;
}
else
{
lean_object* v_val_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2609_; 
v_val_2574_ = lean_ctor_get(v_code_x3f_2295_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_code_x3f_2295_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2576_ = v_code_x3f_2295_;
v_isShared_2577_ = v_isSharedCheck_2609_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_val_2574_);
lean_dec(v_code_x3f_2295_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2609_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
switch(lean_obj_tag(v_val_2574_))
{
case 2:
{
lean_object* v_n_2578_; lean_object* v_mantissa_2579_; lean_object* v_exponent_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_n_2578_ = lean_ctor_get(v_val_2574_, 0);
v_mantissa_2579_ = lean_ctor_get(v_n_2578_, 0);
v_exponent_2580_ = lean_ctor_get(v_n_2578_, 1);
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = lean_nat_dec_eq(v_exponent_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_del_object(v___x_2576_);
v___y_2554_ = v___y_2572_;
v___y_2555_ = v_____do__lift_2571_;
v___y_2556_ = v___y_2569_;
v___y_2557_ = v___y_2570_;
v_j_2558_ = v_val_2574_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2594_; 
lean_inc(v_mantissa_2579_);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_val_2574_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_val_2574_, 0);
lean_dec(v_unused_2595_);
v___x_2584_ = v_val_2574_;
v_isShared_2585_ = v_isSharedCheck_2594_;
goto v_resetjp_2583_;
}
else
{
lean_dec(v_val_2574_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2594_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
lean_ctor_set(v___x_2584_, 0, v_mantissa_2579_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_mantissa_2579_);
v___x_2587_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2587_);
v___x_2589_ = v___x_2576_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_9830__overap_2590_; lean_object* v___x_2591_; 
lean_inc_ref(v___x_2290_);
v___x_9830__overap_2590_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2589_);
lean_inc_ref(v___y_2572_);
v___x_2591_ = lean_apply_1(v___x_9830__overap_2590_, v___y_2572_);
v___y_2538_ = v___y_2572_;
v___y_2539_ = v_____do__lift_2571_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___x_2591_;
goto v___jp_2537_;
}
}
}
}
}
case 3:
{
lean_object* v_s_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2608_; 
v_s_2596_ = lean_ctor_get(v_val_2574_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_val_2574_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2598_ = v_val_2574_;
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_s_2596_);
lean_dec(v_val_2574_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set_tag(v___x_2598_, 1);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_s_2596_);
v___x_2601_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2601_);
v___x_2603_ = v___x_2576_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_9834__overap_2604_; lean_object* v___x_2605_; 
lean_inc_ref(v___x_2290_);
v___x_9834__overap_2604_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2603_);
lean_inc_ref(v___y_2572_);
v___x_2605_ = lean_apply_1(v___x_9834__overap_2604_, v___y_2572_);
v___y_2538_ = v___y_2572_;
v___y_2539_ = v_____do__lift_2571_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___x_2605_;
goto v___jp_2537_;
}
}
}
}
default: 
{
lean_del_object(v___x_2576_);
v___y_2554_ = v___y_2572_;
v___y_2555_ = v_____do__lift_2571_;
v___y_2556_ = v___y_2569_;
v___y_2557_ = v___y_2570_;
v_j_2558_ = v_val_2574_;
goto v___jp_2553_;
}
}
}
}
}
v___jp_2610_:
{
if (lean_obj_tag(v_isSilent_x3f_2294_) == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_box(0);
v___y_2569_ = v_____do__lift_2612_;
v___y_2570_ = v___y_2611_;
v_____do__lift_2571_ = v___x_2614_;
v___y_2572_ = v___y_2613_;
goto v___jp_2568_;
}
else
{
lean_object* v_val_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2634_; 
v_val_2615_ = lean_ctor_get(v_isSilent_x3f_2294_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_isSilent_x3f_2294_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2617_ = v_isSilent_x3f_2294_;
v_isShared_2618_ = v_isSharedCheck_2634_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_val_2615_);
lean_dec(v_isSilent_x3f_2294_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2634_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_9839__overap_2620_; lean_object* v___x_2621_; 
v___x_2619_ = l_Lean_Json_getBool_x3f(v_val_2615_);
lean_dec(v_val_2615_);
lean_inc_ref(v___x_2290_);
v___x_9839__overap_2620_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2619_);
lean_inc_ref(v___y_2613_);
v___x_2621_ = lean_apply_1(v___x_9839__overap_2620_, v___y_2613_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_del_object(v___x_2617_);
lean_dec_ref(v___y_2613_);
lean_dec(v_____do__lift_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec(v_source_x3f_2296_);
lean_dec(v_code_x3f_2295_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_inst_2263_);
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; 
v_a_2630_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2621_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_a_2630_);
v___x_2632_ = v___x_2617_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v___y_2569_ = v_____do__lift_2612_;
v___y_2570_ = v___y_2611_;
v_____do__lift_2571_ = v___x_2632_;
v___y_2572_ = v___y_2613_;
goto v___jp_2568_;
}
}
}
}
}
v___jp_2635_:
{
if (lean_obj_tag(v___y_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___f_2457_);
lean_dec_ref(v___f_2414_);
lean_dec_ref(v___f_2370_);
lean_del_object(v___x_2318_);
lean_dec(v_a_2316_);
lean_del_object(v___x_2303_);
lean_dec(v_data_x3f_2301_);
lean_dec(v_relatedInformation_x3f_2300_);
lean_dec(v_leanTags_x3f_2299_);
lean_dec(v_tags_x3f_2298_);
lean_dec(v_message_2297_);
lean_dec(v_source_x3f_2296_);
lean_dec(v_code_x3f_2295_);
lean_dec(v_isSilent_x3f_2294_);
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_inst_2263_);
v_a_2639_ = lean_ctor_get(v___y_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___y_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___y_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___y_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___y_2638_);
v___x_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_a_2647_);
v___y_2611_ = v___y_2637_;
v_____do__lift_2612_ = v___x_2648_;
v___y_2613_ = v___y_2636_;
goto v___jp_2610_;
}
}
v___jp_2649_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_9883__overap_2660_; lean_object* v___x_2661_; 
v___x_2653_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2654_ = lean_unsigned_to_nat(80u);
v___x_2655_ = l_Lean_Json_pretty(v___y_2650_, v___x_2654_);
v___x_2656_ = lean_string_append(v___x_2653_, v___x_2655_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2658_ = lean_string_append(v___x_2656_, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_inc_ref(v___x_2290_);
v___x_9883__overap_2660_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2659_);
lean_inc_ref(v___y_2651_);
v___x_2661_ = lean_apply_1(v___x_9883__overap_2660_, v___y_2651_);
v___y_2636_ = v___y_2651_;
v___y_2637_ = v___y_2652_;
v___y_2638_ = v___x_2661_;
goto v___jp_2635_;
}
v___jp_2662_:
{
if (lean_obj_tag(v_severity_x3f_2293_) == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_box(0);
v___y_2611_ = v_____do__lift_2663_;
v_____do__lift_2612_ = v___x_2665_;
v___y_2613_ = v___y_2664_;
goto v___jp_2610_;
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2667_; 
v_val_2666_ = lean_ctor_get(v_severity_x3f_2293_, 0);
lean_inc(v_val_2666_);
lean_dec_ref(v_severity_x3f_2293_);
lean_inc(v_val_2666_);
v___x_2667_ = l_Lean_Json_getNat_x3f(v_val_2666_);
if (lean_obj_tag(v___x_2667_) == 1)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = lean_unsigned_to_nat(1u);
v___x_2670_ = lean_nat_dec_eq(v_a_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = lean_unsigned_to_nat(2u);
v___x_2672_ = lean_nat_dec_eq(v_a_2668_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = lean_unsigned_to_nat(3u);
v___x_2674_ = lean_nat_dec_eq(v_a_2668_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_unsigned_to_nat(4u);
v___x_2676_ = lean_nat_dec_eq(v_a_2668_, v___x_2675_);
lean_dec(v_a_2668_);
if (v___x_2676_ == 0)
{
v___y_2650_ = v_val_2666_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v_____do__lift_2663_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_9896__overap_2678_; lean_object* v___x_2679_; 
lean_dec(v_val_2666_);
v___x_2677_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2290_);
v___x_9896__overap_2678_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2677_);
lean_inc_ref(v___y_2664_);
v___x_2679_ = lean_apply_1(v___x_9896__overap_2678_, v___y_2664_);
v___y_2636_ = v___y_2664_;
v___y_2637_ = v_____do__lift_2663_;
v___y_2638_ = v___x_2679_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_9899__overap_2681_; lean_object* v___x_2682_; 
lean_dec(v_a_2668_);
lean_dec(v_val_2666_);
v___x_2680_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2290_);
v___x_9899__overap_2681_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2680_);
lean_inc_ref(v___y_2664_);
v___x_2682_ = lean_apply_1(v___x_9899__overap_2681_, v___y_2664_);
v___y_2636_ = v___y_2664_;
v___y_2637_ = v_____do__lift_2663_;
v___y_2638_ = v___x_2682_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_9902__overap_2684_; lean_object* v___x_2685_; 
lean_dec(v_a_2668_);
lean_dec(v_val_2666_);
v___x_2683_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2290_);
v___x_9902__overap_2684_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2683_);
lean_inc_ref(v___y_2664_);
v___x_2685_ = lean_apply_1(v___x_9902__overap_2684_, v___y_2664_);
v___y_2636_ = v___y_2664_;
v___y_2637_ = v_____do__lift_2663_;
v___y_2638_ = v___x_2685_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_9905__overap_2687_; lean_object* v___x_2688_; 
lean_dec(v_a_2668_);
lean_dec(v_val_2666_);
v___x_2686_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2290_);
v___x_9905__overap_2687_ = l_MonadExcept_ofExcept___redArg(v___x_2280_, v___x_2290_, v___x_2686_);
lean_inc_ref(v___y_2664_);
v___x_2688_ = lean_apply_1(v___x_9905__overap_2687_, v___y_2664_);
v___y_2636_ = v___y_2664_;
v___y_2637_ = v_____do__lift_2663_;
v___y_2638_ = v___x_2688_;
goto v___jp_2635_;
}
}
else
{
lean_dec_ref(v___x_2667_);
v___y_2650_ = v_val_2666_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v_____do__lift_2663_;
goto v___jp_2649_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2716_, lean_object* v_inst_2717_, lean_object* v_j_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2717_, v_j_2718_, v_a_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object* v_inst_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_inc_ref(v_inst_2721_);
v___x_2722_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___x_2722_, 0, lean_box(0));
lean_closure_set(v___x_2722_, 1, v_inst_2721_);
v___x_2723_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___x_2723_, 0, lean_box(0));
lean_closure_set(v___x_2723_, 1, v_inst_2721_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object* v_00_u03b1_2725_, lean_object* v_inst_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(v_inst_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
switch(lean_obj_tag(v_x_2731_))
{
case 0:
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2741_; 
v_a_2733_ = lean_ctor_get(v_x_2731_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2735_ = v_x_2731_;
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v_x_2731_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_a_2733_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2737_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
case 1:
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2753_; 
v_a_2742_ = lean_ctor_get(v_x_2731_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2744_ = v_x_2731_;
v_isShared_2745_ = v_isSharedCheck_2753_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v_x_2731_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2753_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2746_ = l_Lean_Widget_InteractiveGoal_pretty(v_a_2742_);
v___x_2747_ = l_Std_Format_defWidth;
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = l_Std_Format_pretty(v___x_2746_, v___x_2747_, v___x_2748_, v___x_2748_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2749_);
v___x_2751_ = v___x_2744_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
case 2:
{
lean_object* v_alt_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_alt_2754_ = lean_ctor_get(v_x_2731_, 1);
lean_inc_ref(v_alt_2754_);
lean_dec_ref(v_x_2731_);
v___x_2755_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_alt_2754_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
default: 
{
lean_object* v___x_2757_; 
lean_dec_ref(v_x_2731_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1));
return v___x_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(v_x_2758_, v_x_2759_);
lean_dec_ref(v_x_2759_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object* v_tt_2761_){
_start:
{
lean_object* v___f_2762_; lean_object* v_tt_2763_; lean_object* v___x_2764_; 
v___f_2762_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed), 2, 0);
v_tt_2763_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_2762_, v_tt_2761_);
v___x_2764_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object* v_diag_2765_){
_start:
{
lean_object* v_range_2766_; lean_object* v_fullRange_x3f_2767_; lean_object* v_severity_x3f_2768_; lean_object* v_isSilent_x3f_2769_; lean_object* v_code_x3f_2770_; lean_object* v_source_x3f_2771_; lean_object* v_message_2772_; lean_object* v_tags_x3f_2773_; lean_object* v_leanTags_x3f_2774_; lean_object* v_relatedInformation_x3f_2775_; lean_object* v_data_x3f_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2784_; 
v_range_2766_ = lean_ctor_get(v_diag_2765_, 0);
v_fullRange_x3f_2767_ = lean_ctor_get(v_diag_2765_, 1);
v_severity_x3f_2768_ = lean_ctor_get(v_diag_2765_, 2);
v_isSilent_x3f_2769_ = lean_ctor_get(v_diag_2765_, 3);
v_code_x3f_2770_ = lean_ctor_get(v_diag_2765_, 4);
v_source_x3f_2771_ = lean_ctor_get(v_diag_2765_, 5);
v_message_2772_ = lean_ctor_get(v_diag_2765_, 6);
v_tags_x3f_2773_ = lean_ctor_get(v_diag_2765_, 7);
v_leanTags_x3f_2774_ = lean_ctor_get(v_diag_2765_, 8);
v_relatedInformation_x3f_2775_ = lean_ctor_get(v_diag_2765_, 9);
v_data_x3f_2776_ = lean_ctor_get(v_diag_2765_, 10);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_diag_2765_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2778_ = v_diag_2765_;
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_data_x3f_2776_);
lean_inc(v_relatedInformation_x3f_2775_);
lean_inc(v_leanTags_x3f_2774_);
lean_inc(v_tags_x3f_2773_);
lean_inc(v_message_2772_);
lean_inc(v_source_x3f_2771_);
lean_inc(v_code_x3f_2770_);
lean_inc(v_isSilent_x3f_2769_);
lean_inc(v_severity_x3f_2768_);
lean_inc(v_fullRange_x3f_2767_);
lean_inc(v_range_2766_);
lean_dec(v_diag_2765_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_message_2772_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 6, v___x_2780_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_range_2766_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_fullRange_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2783_, 2, v_severity_x3f_2768_);
lean_ctor_set(v_reuseFailAlloc_2783_, 3, v_isSilent_x3f_2769_);
lean_ctor_set(v_reuseFailAlloc_2783_, 4, v_code_x3f_2770_);
lean_ctor_set(v_reuseFailAlloc_2783_, 5, v_source_x3f_2771_);
lean_ctor_set(v_reuseFailAlloc_2783_, 6, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2783_, 7, v_tags_x3f_2773_);
lean_ctor_set(v_reuseFailAlloc_2783_, 8, v_leanTags_x3f_2774_);
lean_ctor_set(v_reuseFailAlloc_2783_, 9, v_relatedInformation_x3f_2775_);
lean_ctor_set(v_reuseFailAlloc_2783_, 10, v_data_x3f_2776_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object* v_nCtx_2785_, lean_object* v_ctx_2786_){
_start:
{
lean_object* v_env_2787_; lean_object* v_mctx_2788_; lean_object* v_lctx_2789_; lean_object* v_opts_2790_; lean_object* v_currNamespace_2791_; lean_object* v_openDecls_2792_; lean_object* v___x_2793_; 
v_env_2787_ = lean_ctor_get(v_ctx_2786_, 0);
v_mctx_2788_ = lean_ctor_get(v_ctx_2786_, 1);
v_lctx_2789_ = lean_ctor_get(v_ctx_2786_, 2);
v_opts_2790_ = lean_ctor_get(v_ctx_2786_, 3);
v_currNamespace_2791_ = lean_ctor_get(v_nCtx_2785_, 0);
v_openDecls_2792_ = lean_ctor_get(v_nCtx_2785_, 1);
lean_inc(v_openDecls_2792_);
lean_inc(v_currNamespace_2791_);
lean_inc_ref(v_opts_2790_);
lean_inc_ref(v_lctx_2789_);
lean_inc_ref(v_mctx_2788_);
lean_inc_ref(v_env_2787_);
v___x_2793_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2793_, 0, v_env_2787_);
lean_ctor_set(v___x_2793_, 1, v_mctx_2788_);
lean_ctor_set(v___x_2793_, 2, v_lctx_2789_);
lean_ctor_set(v___x_2793_, 3, v_opts_2790_);
lean_ctor_set(v___x_2793_, 4, v_currNamespace_2791_);
lean_ctor_set(v___x_2793_, 5, v_openDecls_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object* v_nCtx_2794_, lean_object* v_ctx_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_2794_, v_ctx_2795_);
lean_dec_ref(v_ctx_2795_);
lean_dec_ref(v_nCtx_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx(lean_object* v_x_2797_){
_start:
{
switch(lean_obj_tag(v_x_2797_))
{
case 0:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
return v___x_2798_;
}
case 1:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_unsigned_to_nat(1u);
return v___x_2799_;
}
case 2:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_unsigned_to_nat(2u);
return v___x_2800_;
}
case 3:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_unsigned_to_nat(3u);
return v___x_2801_;
}
default: 
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_unsigned_to_nat(4u);
return v___x_2802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___boxed(lean_object* v_x_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx(v_x_2803_);
lean_dec(v_x_2803_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(lean_object* v_t_2805_, lean_object* v_k_2806_){
_start:
{
switch(lean_obj_tag(v_t_2805_))
{
case 1:
{
lean_object* v_ctx_2807_; lean_object* v_lctx_2808_; lean_object* v_g_2809_; lean_object* v___x_2810_; 
v_ctx_2807_ = lean_ctor_get(v_t_2805_, 0);
lean_inc_ref(v_ctx_2807_);
v_lctx_2808_ = lean_ctor_get(v_t_2805_, 1);
lean_inc_ref(v_lctx_2808_);
v_g_2809_ = lean_ctor_get(v_t_2805_, 2);
lean_inc(v_g_2809_);
lean_dec_ref(v_t_2805_);
v___x_2810_ = lean_apply_3(v_k_2806_, v_ctx_2807_, v_lctx_2808_, v_g_2809_);
return v___x_2810_;
}
case 3:
{
lean_object* v_cls_2811_; lean_object* v_msg_2812_; uint8_t v_collapsed_2813_; lean_object* v_children_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_cls_2811_ = lean_ctor_get(v_t_2805_, 0);
lean_inc(v_cls_2811_);
v_msg_2812_ = lean_ctor_get(v_t_2805_, 1);
lean_inc(v_msg_2812_);
v_collapsed_2813_ = lean_ctor_get_uint8(v_t_2805_, sizeof(void*)*3);
v_children_2814_ = lean_ctor_get(v_t_2805_, 2);
lean_inc_ref(v_children_2814_);
lean_dec_ref(v_t_2805_);
v___x_2815_ = lean_box(v_collapsed_2813_);
v___x_2816_ = lean_apply_4(v_k_2806_, v_cls_2811_, v_msg_2812_, v___x_2815_, v_children_2814_);
return v___x_2816_;
}
case 4:
{
return v_k_2806_;
}
default: 
{
lean_object* v_ctx_2817_; lean_object* v_infos_2818_; lean_object* v___x_2819_; 
v_ctx_2817_ = lean_ctor_get(v_t_2805_, 0);
lean_inc_ref(v_ctx_2817_);
v_infos_2818_ = lean_ctor_get(v_t_2805_, 1);
lean_inc(v_infos_2818_);
lean_dec(v_t_2805_);
v___x_2819_ = lean_apply_2(v_k_2806_, v_ctx_2817_, v_infos_2818_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(lean_object* v_motive_2820_, lean_object* v_ctorIdx_2821_, lean_object* v_t_2822_, lean_object* v_h_2823_, lean_object* v_k_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2822_, v_k_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___boxed(lean_object* v_motive_2826_, lean_object* v_ctorIdx_2827_, lean_object* v_t_2828_, lean_object* v_h_2829_, lean_object* v_k_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim(v_motive_2826_, v_ctorIdx_2827_, v_t_2828_, v_h_2829_, v_k_2830_);
lean_dec(v_ctorIdx_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim___redArg(lean_object* v_t_2832_, lean_object* v_code_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2832_, v_code_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_code_elim(lean_object* v_motive_2835_, lean_object* v_t_2836_, lean_object* v_h_2837_, lean_object* v_code_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2836_, v_code_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim___redArg(lean_object* v_t_2840_, lean_object* v_goal_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2840_, v_goal_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_goal_elim(lean_object* v_motive_2843_, lean_object* v_t_2844_, lean_object* v_h_2845_, lean_object* v_goal_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2844_, v_goal_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim___redArg(lean_object* v_t_2848_, lean_object* v_widget_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2848_, v_widget_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_widget_elim(lean_object* v_motive_2851_, lean_object* v_t_2852_, lean_object* v_h_2853_, lean_object* v_widget_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2852_, v_widget_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim___redArg(lean_object* v_t_2856_, lean_object* v_trace_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2856_, v_trace_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_trace_elim(lean_object* v_motive_2859_, lean_object* v_t_2860_, lean_object* v_h_2861_, lean_object* v_trace_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2860_, v_trace_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim___redArg(lean_object* v_t_2864_, lean_object* v_ignoreTags_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2864_, v_ignoreTags_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ignoreTags_elim(lean_object* v_motive_2867_, lean_object* v_t_2868_, lean_object* v_h_2869_, lean_object* v_ignoreTags_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorElim___redArg(v_t_2868_, v_ignoreTags_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0(void){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Array_instInhabited(lean_box(0));
return v___x_2872_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__0);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2(void){
_start:
{
lean_object* v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2875_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__1);
v___x_2876_ = 0;
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v___x_2877_);
lean_ctor_set(v___x_2879_, 2, v___x_2875_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*3, v___x_2876_);
return v___x_2879_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default(void){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default___closed__2);
return v___x_2880_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt(void){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default;
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object* v_e_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2885_ = lean_array_get_size(v_a_2883_);
v___x_2886_ = lean_array_push(v_a_2883_, v_e_2882_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed___boxed(lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v_e_2889_, v_a_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object* v_fmt_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2915_; 
v___x_2896_ = lean_box(4);
v___x_2897_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_2896_, v_a_2894_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2915_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2915_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_fst_2902_; lean_object* v_snd_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2914_; 
v_fst_2902_ = lean_ctor_get(v_a_2898_, 0);
v_snd_2903_ = lean_ctor_get(v_a_2898_, 1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2905_ = v_a_2898_;
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snd_2903_);
lean_inc(v_fst_2902_);
lean_dec(v_a_2898_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v_fst_2902_);
lean_ctor_set(v___x_2907_, 1, v_fmt_2893_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_snd_2903_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2909_);
v___x_2911_ = v___x_2900_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags___boxed(lean_object* v_fmt_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_2916_, v_a_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object* v_nCtx_2928_, lean_object* v_ctx_2929_){
_start:
{
lean_object* v_env_2930_; lean_object* v_mctx_2931_; lean_object* v_opts_2932_; lean_object* v_currNamespace_2933_; lean_object* v_openDecls_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_env_2930_ = lean_ctor_get(v_ctx_2929_, 0);
v_mctx_2931_ = lean_ctor_get(v_ctx_2929_, 1);
v_opts_2932_ = lean_ctor_get(v_ctx_2929_, 3);
v_currNamespace_2933_ = lean_ctor_get(v_nCtx_2928_, 0);
v_openDecls_2934_ = lean_ctor_get(v_nCtx_2928_, 1);
v___x_2935_ = lean_box(0);
v___x_2936_ = l_Lean_instInhabitedFileMap_default;
v___x_2937_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2));
lean_inc(v_openDecls_2934_);
lean_inc(v_currNamespace_2933_);
lean_inc_ref(v_opts_2932_);
lean_inc_ref(v_mctx_2931_);
lean_inc_ref(v_env_2930_);
v___x_2938_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2938_, 0, v_env_2930_);
lean_ctor_set(v___x_2938_, 1, v___x_2935_);
lean_ctor_set(v___x_2938_, 2, v___x_2936_);
lean_ctor_set(v___x_2938_, 3, v_mctx_2931_);
lean_ctor_set(v___x_2938_, 4, v_opts_2932_);
lean_ctor_set(v___x_2938_, 5, v_currNamespace_2933_);
lean_ctor_set(v___x_2938_, 6, v_openDecls_2934_);
lean_ctor_set(v___x_2938_, 7, v___x_2937_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3));
v___x_2940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2935_);
lean_ctor_set(v___x_2940_, 2, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object* v_nCtx_2941_, lean_object* v_ctx_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_2941_, v_ctx_2942_);
lean_dec_ref(v_ctx_2942_);
lean_dec_ref(v_nCtx_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(lean_object* v_a_2944_, lean_object* v_b_2945_){
_start:
{
lean_object* v_array_2946_; lean_object* v_start_2947_; lean_object* v_stop_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2961_; 
v_array_2946_ = lean_ctor_get(v_a_2944_, 0);
v_start_2947_ = lean_ctor_get(v_a_2944_, 1);
v_stop_2948_ = lean_ctor_get(v_a_2944_, 2);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2950_ = v_a_2944_;
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_stop_2948_);
lean_inc(v_start_2947_);
lean_inc(v_array_2946_);
lean_dec(v_a_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2961_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_nat_dec_lt(v_start_2947_, v_stop_2948_);
if (v___x_2952_ == 0)
{
lean_del_object(v___x_2950_);
lean_dec(v_stop_2948_);
lean_dec(v_start_2947_);
lean_dec_ref(v_array_2946_);
return v_b_2945_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2953_ = lean_unsigned_to_nat(1u);
v___x_2954_ = lean_nat_add(v_start_2947_, v___x_2953_);
lean_inc_ref(v_array_2946_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2954_);
v___x_2956_ = v___x_2950_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_array_2946_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_stop_2948_);
v___x_2956_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_array_fget(v_array_2946_, v_start_2947_);
lean_dec(v_start_2947_);
lean_dec_ref(v_array_2946_);
v___x_2958_ = lean_array_push(v_b_2945_, v___x_2957_);
v_a_2944_ = v___x_2956_;
v_b_2945_ = v___x_2958_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1(void){
_start:
{
lean_object* v___x_2964_; double v___x_2965_; 
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = lean_float_of_nat(v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object* v_cls_2970_, lean_object* v_blockSize_2971_, lean_object* v_children_2972_){
_start:
{
lean_object* v___x_2973_; uint8_t v___y_2975_; uint8_t v___x_2997_; 
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_nat_dec_lt(v___x_2973_, v_blockSize_2971_);
if (v___x_2997_ == 0)
{
v___y_2975_ = v___x_2997_;
goto v___jp_2974_;
}
else
{
lean_object* v_start_2998_; lean_object* v_stop_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_start_2998_ = lean_ctor_get(v_children_2972_, 1);
v_stop_2999_ = lean_ctor_get(v_children_2972_, 2);
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = lean_nat_add(v_blockSize_2971_, v___x_3000_);
v___x_3002_ = lean_nat_sub(v_stop_2999_, v_start_2998_);
v___x_3003_ = lean_nat_dec_lt(v___x_3001_, v___x_3002_);
lean_dec(v___x_3002_);
lean_dec(v___x_3001_);
v___y_2975_ = v___x_3003_;
goto v___jp_2974_;
}
v___jp_2974_:
{
if (v___y_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v_cls_2970_);
v___x_2976_ = l_Subarray_copy___redArg(v_children_2972_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v_more_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; double v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_start_2984_; lean_object* v_stop_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_inc_ref(v_children_2972_);
v___x_2977_ = l_Subarray_drop___redArg(v_children_2972_, v_blockSize_2971_);
lean_inc(v_cls_2970_);
v_more_2978_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_2970_, v_blockSize_2971_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0));
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_2982_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2));
v___x_2983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2983_, 0, v_cls_2970_);
lean_ctor_set(v___x_2983_, 1, v___x_2980_);
lean_ctor_set(v___x_2983_, 2, v___x_2982_);
lean_ctor_set_float(v___x_2983_, sizeof(void*)*3, v___x_2981_);
lean_ctor_set_float(v___x_2983_, sizeof(void*)*3 + 8, v___x_2981_);
lean_ctor_set_uint8(v___x_2983_, sizeof(void*)*3 + 16, v___y_2975_);
v_start_2984_ = lean_ctor_get(v_children_2972_, 1);
lean_inc(v_start_2984_);
v_stop_2985_ = lean_ctor_get(v_children_2972_, 2);
lean_inc(v_stop_2985_);
v___x_2986_ = l_Subarray_take___redArg(v_children_2972_, v_blockSize_2971_);
v___x_2987_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v___x_2986_, v___x_2979_);
v___x_2988_ = lean_nat_sub(v_stop_2985_, v_start_2984_);
lean_dec(v_start_2984_);
lean_dec(v_stop_2985_);
v___x_2989_ = lean_nat_sub(v___x_2988_, v_blockSize_2971_);
lean_dec(v___x_2988_);
v___x_2990_ = l_Nat_reprFast(v___x_2989_);
v___x_2991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
v___x_2992_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4));
v___x_2993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l_Lean_MessageData_ofFormat(v___x_2993_);
v___x_2995_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2983_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
lean_ctor_set(v___x_2995_, 2, v_more_2978_);
v___x_2996_ = lean_array_push(v___x_2987_, v___x_2995_);
return v___x_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object* v_cls_3004_, lean_object* v_blockSize_3005_, lean_object* v_children_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3004_, v_blockSize_3005_, v_children_3006_);
lean_dec(v_blockSize_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0(lean_object* v_inst_3008_, lean_object* v_R_3009_, lean_object* v_a_3010_, lean_object* v_b_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v_a_3010_, v_b_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(lean_object* v_opts_3013_, lean_object* v_opt_3014_){
_start:
{
lean_object* v_name_3015_; lean_object* v_map_3016_; lean_object* v___x_3017_; 
v_name_3015_ = lean_ctor_get(v_opt_3014_, 0);
v_map_3016_ = lean_ctor_get(v_opts_3013_, 0);
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3016_, v_name_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_box(0);
return v___x_3018_;
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3028_; 
v_val_3019_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3021_ = v___x_3017_;
v_isShared_3022_ = v_isSharedCheck_3028_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_val_3019_);
lean_dec(v___x_3017_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3028_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
if (lean_obj_tag(v_val_3019_) == 3)
{
lean_object* v_v_3023_; lean_object* v___x_3025_; 
v_v_3023_ = lean_ctor_get(v_val_3019_, 0);
lean_inc(v_v_3023_);
lean_dec_ref(v_val_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v_v_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_v_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_object* v___x_3027_; 
lean_del_object(v___x_3021_);
lean_dec(v_val_3019_);
v___x_3027_ = lean_box(0);
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2___boxed(lean_object* v_opts_3029_, lean_object* v_opt_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3029_, v_opt_3030_);
lean_dec_ref(v_opt_3030_);
lean_dec_ref(v_opts_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object* v_a_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_nat_to_int(v_a_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object* v_ctx_3034_, lean_object* v_nCtx_3035_, size_t v_sz_3036_, size_t v_i_3037_, lean_object* v_bs_3038_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
if (v___x_3039_ == 0)
{
lean_dec_ref(v_nCtx_3035_);
return v_bs_3038_;
}
else
{
lean_object* v_v_3040_; lean_object* v___x_3041_; lean_object* v_bs_x27_3042_; lean_object* v___y_3044_; 
v_v_3040_ = lean_array_uget(v_bs_3038_, v_i_3037_);
v___x_3041_ = lean_unsigned_to_nat(0u);
v_bs_x27_3042_ = lean_array_uset(v_bs_3038_, v_i_3037_, v___x_3041_);
if (lean_obj_tag(v_ctx_3034_) == 0)
{
lean_object* v___x_3049_; 
lean_inc_ref(v_nCtx_3035_);
v___x_3049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_nCtx_3035_);
lean_ctor_set(v___x_3049_, 1, v_v_3040_);
v___y_3044_ = v___x_3049_;
goto v___jp_3043_;
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_val_3050_ = lean_ctor_get(v_ctx_3034_, 0);
lean_inc(v_val_3050_);
v___x_3051_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3051_, 0, v_val_3050_);
lean_ctor_set(v___x_3051_, 1, v_v_3040_);
lean_inc_ref(v_nCtx_3035_);
v___x_3052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_nCtx_3035_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___y_3044_ = v___x_3052_;
goto v___jp_3043_;
}
v___jp_3043_:
{
size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((size_t)1ULL);
v___x_3046_ = lean_usize_add(v_i_3037_, v___x_3045_);
v___x_3047_ = lean_array_uset(v_bs_x27_3042_, v_i_3037_, v___y_3044_);
v_i_3037_ = v___x_3046_;
v_bs_3038_ = v___x_3047_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object* v_ctx_3053_, lean_object* v_nCtx_3054_, lean_object* v_sz_3055_, lean_object* v_i_3056_, lean_object* v_bs_3057_){
_start:
{
size_t v_sz_boxed_3058_; size_t v_i_boxed_3059_; lean_object* v_res_3060_; 
v_sz_boxed_3058_ = lean_unbox_usize(v_sz_3055_);
lean_dec(v_sz_3055_);
v_i_boxed_3059_ = lean_unbox_usize(v_i_3056_);
lean_dec(v_i_3056_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v_ctx_3053_, v_nCtx_3054_, v_sz_boxed_3058_, v_i_boxed_3059_, v_bs_3057_);
lean_dec(v_ctx_3053_);
return v_res_3060_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_unsigned_to_nat(4u);
v___x_3068_ = lean_nat_to_int(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5));
v___x_3071_ = lean_mk_io_user_error(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object* v_nCtx_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_ctx_3081_; lean_object* v_n_3082_; lean_object* v_d_3083_; lean_object* v___y_3084_; uint8_t v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v_nodes_3109_; lean_object* v___y_3110_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; uint8_t v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3161_; uint8_t v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3198_; uint8_t v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_header_3203_; lean_object* v___y_3204_; double v___y_3209_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; uint8_t v___y_3213_; double v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v_ctx_3227_; lean_object* v_data_3228_; lean_object* v_header_3229_; lean_object* v_children_3230_; lean_object* v___y_3231_; lean_object* v_ctx_3282_; lean_object* v_wi_3283_; lean_object* v_d_3284_; lean_object* v___y_3285_; lean_object* v_ctx_3326_; lean_object* v_d_3327_; lean_object* v___y_3328_; lean_object* v_ctx_3332_; lean_object* v_d_u2081_3333_; lean_object* v_d_u2082_3334_; lean_object* v___y_3335_; lean_object* v_ctx_3366_; lean_object* v_d_3367_; lean_object* v___y_3368_; lean_object* v___x_3389_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; 
v___x_3389_ = l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_;
if (lean_obj_tag(v_a_3076_) == 0)
{
switch(lean_obj_tag(v_a_3077_))
{
case 0:
{
lean_object* v_a_3401_; lean_object* v_fmt_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_nCtx_3075_);
v_a_3401_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3401_);
lean_dec_ref(v_a_3077_);
v_fmt_3402_ = lean_ctor_get(v_a_3401_, 0);
lean_inc(v_fmt_3402_);
lean_dec_ref(v_a_3401_);
v___x_3403_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_3402_, v_a_3078_);
return v___x_3403_;
}
case 1:
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v_nCtx_3075_);
v_a_3404_ = lean_ctor_get(v_a_3077_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_a_3077_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3406_ = v_a_3077_;
v_isShared_3407_ = v_isSharedCheck_3417_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v_a_3077_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3417_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3408_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8));
v___x_3409_ = l_Lean_mkMVar(v_a_3404_);
v___x_3410_ = lean_expr_dbg_to_string(v___x_3409_);
lean_dec_ref(v___x_3409_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 3);
lean_ctor_set(v___x_3406_, 0, v___x_3410_);
v___x_3412_ = v___x_3406_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3408_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v_a_3078_);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
return v___x_3415_;
}
}
}
case 2:
{
lean_object* v_a_3418_; lean_object* v_a_3419_; 
v_a_3418_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3418_);
v_a_3419_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3419_);
lean_dec_ref(v_a_3077_);
v_ctx_3282_ = v_a_3076_;
v_wi_3283_ = v_a_3418_;
v_d_3284_ = v_a_3419_;
v___y_3285_ = v_a_3078_;
goto v___jp_3281_;
}
case 3:
{
lean_object* v_a_3420_; lean_object* v_a_3421_; 
v_a_3420_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3420_);
v_a_3421_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3421_);
lean_dec_ref(v_a_3077_);
v_ctx_3326_ = v_a_3420_;
v_d_3327_ = v_a_3421_;
v___y_3328_ = v_a_3078_;
goto v___jp_3325_;
}
case 4:
{
lean_object* v_a_3422_; lean_object* v_a_3423_; 
lean_dec_ref(v_nCtx_3075_);
v_a_3422_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3422_);
v_a_3423_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3423_);
lean_dec_ref(v_a_3077_);
v_nCtx_3075_ = v_a_3422_;
v_a_3077_ = v_a_3423_;
goto _start;
}
case 5:
{
lean_object* v_a_3425_; lean_object* v_a_3426_; 
v_a_3425_ = lean_ctor_get(v_a_3077_, 0);
lean_inc(v_a_3425_);
v_a_3426_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3426_);
lean_dec_ref(v_a_3077_);
v_ctx_3081_ = v_a_3076_;
v_n_3082_ = v_a_3425_;
v_d_3083_ = v_a_3426_;
v___y_3084_ = v_a_3078_;
goto v___jp_3080_;
}
case 6:
{
lean_object* v_a_3427_; 
v_a_3427_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3427_);
lean_dec_ref(v_a_3077_);
v_ctx_3366_ = v_a_3076_;
v_d_3367_ = v_a_3427_;
v___y_3368_ = v_a_3078_;
goto v___jp_3365_;
}
case 7:
{
lean_object* v_a_3428_; lean_object* v_a_3429_; 
v_a_3428_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3428_);
v_a_3429_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3429_);
lean_dec_ref(v_a_3077_);
v_ctx_3332_ = v_a_3076_;
v_d_u2081_3333_ = v_a_3428_;
v_d_u2082_3334_ = v_a_3429_;
v___y_3335_ = v_a_3078_;
goto v___jp_3331_;
}
case 8:
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3430_);
lean_dec_ref(v_a_3077_);
v_a_3077_ = v_a_3430_;
goto _start;
}
case 9:
{
lean_object* v_data_3432_; lean_object* v_msg_3433_; lean_object* v_children_3434_; 
v_data_3432_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_data_3432_);
v_msg_3433_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_msg_3433_);
v_children_3434_ = lean_ctor_get(v_a_3077_, 2);
lean_inc_ref(v_children_3434_);
lean_dec_ref(v_a_3077_);
v_ctx_3227_ = v_a_3076_;
v_data_3228_ = v_data_3432_;
v_header_3229_ = v_msg_3433_;
v_children_3230_ = v_children_3434_;
v___y_3231_ = v_a_3078_;
goto v___jp_3226_;
}
default: 
{
lean_object* v_f_3435_; lean_object* v___x_3436_; 
v_f_3435_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_f_3435_);
lean_dec_ref(v_a_3077_);
v___x_3436_ = lean_box(0);
v___y_3391_ = v_f_3435_;
v___y_3392_ = v_a_3078_;
v___y_3393_ = v_a_3076_;
v___y_3394_ = v___x_3436_;
goto v___jp_3390_;
}
}
}
else
{
switch(lean_obj_tag(v_a_3077_))
{
case 0:
{
lean_object* v_a_3437_; lean_object* v_val_3438_; lean_object* v_fmt_3439_; lean_object* v_infos_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3475_; 
v_a_3437_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3437_);
lean_dec_ref(v_a_3077_);
v_val_3438_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_val_3438_);
lean_dec_ref(v_a_3076_);
v_fmt_3439_ = lean_ctor_get(v_a_3437_, 0);
v_infos_3440_ = lean_ctor_get(v_a_3437_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_a_3437_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3442_ = v_a_3437_;
v_isShared_3443_ = v_isSharedCheck_3475_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_infos_3440_);
lean_inc(v_fmt_3439_);
lean_dec(v_a_3437_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3475_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3444_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3075_, v_val_3438_);
lean_dec(v_val_3438_);
lean_dec_ref(v_nCtx_3075_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_infos_3440_);
v___x_3446_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3446_, v_a_3078_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3465_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3465_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3465_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3464_; 
v_fst_3452_ = lean_ctor_get(v_a_3448_, 0);
v_snd_3453_ = lean_ctor_get(v_a_3448_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3448_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3455_ = v_a_3448_;
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_inc(v_fst_3452_);
lean_dec(v_a_3448_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_fst_3452_);
lean_ctor_set(v___x_3457_, 1, v_fmt_3439_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3459_ = v___x_3455_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_snd_3453_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3459_);
v___x_3461_ = v___x_3450_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_fmt_3439_);
v_a_3466_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3447_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3447_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
}
case 1:
{
lean_object* v_val_3476_; lean_object* v_a_3477_; lean_object* v_lctx_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_val_3476_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_val_3476_);
lean_dec_ref(v_a_3076_);
v_a_3477_ = lean_ctor_get(v_a_3077_, 0);
lean_inc(v_a_3477_);
lean_dec_ref(v_a_3077_);
v_lctx_3478_ = lean_ctor_get(v_val_3476_, 2);
lean_inc_ref(v_lctx_3478_);
v___x_3479_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3075_, v_val_3476_);
lean_dec(v_val_3476_);
lean_dec_ref(v_nCtx_3075_);
v___x_3480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v_lctx_3478_);
lean_ctor_set(v___x_3480_, 2, v_a_3477_);
v___x_3481_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3480_, v_a_3078_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3500_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3500_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3500_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_fst_3486_; lean_object* v_snd_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3499_; 
v_fst_3486_ = lean_ctor_get(v_a_3482_, 0);
v_snd_3487_ = lean_ctor_get(v_a_3482_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3489_ = v_a_3482_;
v_isShared_3490_ = v_isSharedCheck_3499_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snd_3487_);
lean_inc(v_fst_3486_);
lean_dec(v_a_3482_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3499_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_fst_3486_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_snd_3487_);
v___x_3494_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3494_);
v___x_3496_ = v___x_3484_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3481_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3481_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
case 2:
{
lean_object* v_a_3509_; lean_object* v_a_3510_; 
v_a_3509_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3509_);
v_a_3510_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3510_);
lean_dec_ref(v_a_3077_);
v_ctx_3282_ = v_a_3076_;
v_wi_3283_ = v_a_3509_;
v_d_3284_ = v_a_3510_;
v___y_3285_ = v_a_3078_;
goto v___jp_3281_;
}
case 3:
{
lean_object* v_a_3511_; lean_object* v_a_3512_; 
lean_dec_ref(v_a_3076_);
v_a_3511_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3511_);
v_a_3512_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3512_);
lean_dec_ref(v_a_3077_);
v_ctx_3326_ = v_a_3511_;
v_d_3327_ = v_a_3512_;
v___y_3328_ = v_a_3078_;
goto v___jp_3325_;
}
case 4:
{
lean_object* v_a_3513_; lean_object* v_a_3514_; 
lean_dec_ref(v_nCtx_3075_);
v_a_3513_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3513_);
v_a_3514_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3514_);
lean_dec_ref(v_a_3077_);
v_nCtx_3075_ = v_a_3513_;
v_a_3077_ = v_a_3514_;
goto _start;
}
case 5:
{
lean_object* v_a_3516_; lean_object* v_a_3517_; 
v_a_3516_ = lean_ctor_get(v_a_3077_, 0);
lean_inc(v_a_3516_);
v_a_3517_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3517_);
lean_dec_ref(v_a_3077_);
v_ctx_3081_ = v_a_3076_;
v_n_3082_ = v_a_3516_;
v_d_3083_ = v_a_3517_;
v___y_3084_ = v_a_3078_;
goto v___jp_3080_;
}
case 6:
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3518_);
lean_dec_ref(v_a_3077_);
v_ctx_3366_ = v_a_3076_;
v_d_3367_ = v_a_3518_;
v___y_3368_ = v_a_3078_;
goto v___jp_3365_;
}
case 7:
{
lean_object* v_a_3519_; lean_object* v_a_3520_; 
v_a_3519_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_a_3519_);
v_a_3520_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3520_);
lean_dec_ref(v_a_3077_);
v_ctx_3332_ = v_a_3076_;
v_d_u2081_3333_ = v_a_3519_;
v_d_u2082_3334_ = v_a_3520_;
v___y_3335_ = v_a_3078_;
goto v___jp_3331_;
}
case 8:
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_a_3521_);
lean_dec_ref(v_a_3077_);
v_a_3077_ = v_a_3521_;
goto _start;
}
case 9:
{
lean_object* v_data_3523_; lean_object* v_msg_3524_; lean_object* v_children_3525_; 
v_data_3523_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_data_3523_);
v_msg_3524_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_msg_3524_);
v_children_3525_ = lean_ctor_get(v_a_3077_, 2);
lean_inc_ref(v_children_3525_);
lean_dec_ref(v_a_3077_);
v_ctx_3227_ = v_a_3076_;
v_data_3228_ = v_data_3523_;
v_header_3229_ = v_msg_3524_;
v_children_3230_ = v_children_3525_;
v___y_3231_ = v_a_3078_;
goto v___jp_3226_;
}
default: 
{
lean_object* v_val_3526_; lean_object* v_f_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_val_3526_ = lean_ctor_get(v_a_3076_, 0);
v_f_3527_ = lean_ctor_get(v_a_3077_, 0);
lean_inc_ref(v_f_3527_);
lean_dec_ref(v_a_3077_);
v___x_3528_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_3075_, v_val_3526_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
v___y_3391_ = v_f_3527_;
v___y_3392_ = v_a_3078_;
v___y_3393_ = v_a_3076_;
v___y_3394_ = v___x_3529_;
goto v___jp_3390_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3081_, v_d_3083_, v___y_3084_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3104_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3104_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3104_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v_fst_3090_; lean_object* v_snd_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3103_; 
v_fst_3090_ = lean_ctor_get(v_a_3086_, 0);
v_snd_3091_ = lean_ctor_get(v_a_3086_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3093_ = v_a_3086_;
v_isShared_3094_ = v_isSharedCheck_3103_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_snd_3091_);
lean_inc(v_fst_3090_);
lean_dec(v_a_3086_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3103_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3095_ = lean_nat_to_int(v_n_3082_);
v___x_3096_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v_fst_3090_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3096_);
v___x_3098_ = v___x_3093_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_snd_3091_);
v___x_3098_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3100_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3098_);
v___x_3100_ = v___x_3088_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
else
{
lean_dec(v_n_3082_);
return v___x_3085_;
}
}
v___jp_3105_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3111_, 0, v___y_3108_);
lean_ctor_set(v___x_3111_, 1, v___y_3107_);
lean_ctor_set(v___x_3111_, 2, v_nodes_3109_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3, v___y_3106_);
v___x_3112_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3111_, v___y_3110_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3131_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3131_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3131_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v_fst_3117_; lean_object* v_snd_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3130_; 
v_fst_3117_ = lean_ctor_get(v_a_3113_, 0);
v_snd_3118_ = lean_ctor_get(v_a_3113_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3113_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3120_ = v_a_3113_;
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_snd_3118_);
lean_inc(v_fst_3117_);
lean_dec(v_a_3113_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_fst_3117_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3123_);
v___x_3125_ = v___x_3120_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_snd_3118_);
v___x_3125_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3125_);
v___x_3127_ = v___x_3115_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v_a_3132_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3112_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3112_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = lean_array_get_size(v___y_3144_);
v___x_3149_ = l_Array_toSubarray___redArg(v___y_3144_, v___x_3147_, v___x_3148_);
lean_inc(v___y_3145_);
v___x_3150_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v___y_3145_, v___y_3146_, v___x_3149_);
lean_dec(v___y_3146_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
v___y_3106_ = v___y_3141_;
v___y_3107_ = v___y_3142_;
v___y_3108_ = v___y_3145_;
v_nodes_3109_ = v___x_3151_;
v___y_3110_ = v___y_3143_;
goto v___jp_3105_;
}
v___jp_3152_:
{
lean_object* v___x_3158_; lean_object* v_defValue_3159_; 
v___x_3158_ = l_Lean_MessageData_maxTraceChildren;
v_defValue_3159_ = lean_ctor_get(v___x_3158_, 1);
lean_inc(v_defValue_3159_);
v___y_3141_ = v___y_3153_;
v___y_3142_ = v___y_3154_;
v___y_3143_ = v___y_3156_;
v___y_3144_ = v___y_3155_;
v___y_3145_ = v___y_3157_;
v___y_3146_ = v_defValue_3159_;
goto v___jp_3140_;
}
v___jp_3160_:
{
size_t v_sz_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v_sz_3167_ = lean_array_size(v___y_3163_);
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v___y_3161_, v_nCtx_3075_, v_sz_3167_, v___x_3168_, v___y_3163_);
if (lean_obj_tag(v___y_3161_) == 0)
{
v___y_3153_ = v___y_3162_;
v___y_3154_ = v___y_3164_;
v___y_3155_ = v___x_3169_;
v___y_3156_ = v___y_3165_;
v___y_3157_ = v___y_3166_;
goto v___jp_3152_;
}
else
{
lean_object* v_val_3170_; lean_object* v_opts_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v_val_3170_ = lean_ctor_get(v___y_3161_, 0);
lean_inc(v_val_3170_);
lean_dec_ref(v___y_3161_);
v_opts_3171_ = lean_ctor_get(v_val_3170_, 3);
lean_inc_ref(v_opts_3171_);
lean_dec(v_val_3170_);
v___x_3172_ = l_Lean_MessageData_maxTraceChildren;
v___x_3173_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3171_, v___x_3172_);
lean_dec_ref(v_opts_3171_);
if (lean_obj_tag(v___x_3173_) == 0)
{
v___y_3153_ = v___y_3162_;
v___y_3154_ = v___y_3164_;
v___y_3155_ = v___x_3169_;
v___y_3156_ = v___y_3165_;
v___y_3157_ = v___y_3166_;
goto v___jp_3152_;
}
else
{
lean_object* v_val_3174_; 
v_val_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_val_3174_);
lean_dec_ref(v___x_3173_);
v___y_3141_ = v___y_3162_;
v___y_3142_ = v___y_3164_;
v___y_3143_ = v___y_3165_;
v___y_3144_ = v___x_3169_;
v___y_3145_ = v___y_3166_;
v___y_3146_ = v_val_3174_;
goto v___jp_3140_;
}
}
}
v___jp_3175_:
{
size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v_sz_3182_ = lean_array_size(v___y_3178_);
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3075_, v___y_3176_, v_sz_3182_, v___x_3183_, v___y_3178_, v___y_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v_fst_3186_; lean_object* v_snd_3187_; lean_object* v___x_3188_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v_fst_3186_ = lean_ctor_get(v_a_3185_, 0);
lean_inc(v_fst_3186_);
v_snd_3187_ = lean_ctor_get(v_a_3185_, 1);
lean_inc(v_snd_3187_);
lean_dec(v_a_3185_);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_fst_3186_);
v___y_3106_ = v___y_3177_;
v___y_3107_ = v___y_3179_;
v___y_3108_ = v___y_3181_;
v_nodes_3109_ = v___x_3188_;
v___y_3110_ = v_snd_3187_;
goto v___jp_3105_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v___y_3181_);
lean_dec(v___y_3179_);
v_a_3189_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3184_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3184_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
v___jp_3197_:
{
if (v___y_3199_ == 0)
{
v___y_3176_ = v___y_3198_;
v___y_3177_ = v___y_3199_;
v___y_3178_ = v___y_3201_;
v___y_3179_ = v_header_3203_;
v___y_3180_ = v___y_3204_;
v___y_3181_ = v___y_3202_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3205_ = lean_array_get_size(v___y_3201_);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = lean_nat_dec_eq(v___x_3205_, v___x_3206_);
if (v___x_3207_ == 0)
{
v___y_3161_ = v___y_3198_;
v___y_3162_ = v___y_3199_;
v___y_3163_ = v___y_3201_;
v___y_3164_ = v_header_3203_;
v___y_3165_ = v___y_3204_;
v___y_3166_ = v___y_3202_;
goto v___jp_3160_;
}
else
{
if (v___y_3200_ == 0)
{
v___y_3176_ = v___y_3198_;
v___y_3177_ = v___y_3199_;
v___y_3178_ = v___y_3201_;
v___y_3179_ = v_header_3203_;
v___y_3180_ = v___y_3204_;
v___y_3181_ = v___y_3202_;
goto v___jp_3175_;
}
else
{
v___y_3161_ = v___y_3198_;
v___y_3162_ = v___y_3199_;
v___y_3163_ = v___y_3201_;
v___y_3164_ = v_header_3203_;
v___y_3165_ = v___y_3204_;
v___y_3166_ = v___y_3202_;
goto v___jp_3160_;
}
}
}
}
v___jp_3208_:
{
lean_object* v___x_3218_; double v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3218_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1));
v___x_3219_ = lean_float_sub(v___y_3214_, v___y_3209_);
v___x_3220_ = lean_float_to_string(v___x_3219_);
v___x_3221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3218_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3));
v___x_3224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___y_3216_);
v___y_3198_ = v___y_3210_;
v___y_3199_ = v___y_3211_;
v___y_3200_ = v___y_3213_;
v___y_3201_ = v___y_3212_;
v___y_3202_ = v___y_3217_;
v_header_3203_ = v___x_3225_;
v___y_3204_ = v___y_3215_;
goto v___jp_3197_;
}
v___jp_3226_:
{
lean_object* v_cls_3232_; double v_startTime_3233_; double v_stopTime_3234_; uint8_t v_collapsed_3235_; uint8_t v___x_3236_; 
v_cls_3232_ = lean_ctor_get(v_data_3228_, 0);
lean_inc(v_cls_3232_);
v_startTime_3233_ = lean_ctor_get_float(v_data_3228_, sizeof(void*)*3);
v_stopTime_3234_ = lean_ctor_get_float(v_data_3228_, sizeof(void*)*3 + 8);
v_collapsed_3235_ = lean_ctor_get_uint8(v_data_3228_, sizeof(void*)*3 + 16);
lean_dec_ref(v_data_3228_);
v___x_3236_ = l_Lean_Name_isAnonymous(v_cls_3232_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_inc(v_ctx_3227_);
lean_inc_ref(v_nCtx_3075_);
v___x_3237_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3227_, v_header_3229_, v___y_3231_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3250_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3237_);
v_fst_3239_ = lean_ctor_get(v_a_3238_, 0);
v_snd_3240_ = lean_ctor_get(v_a_3238_, 1);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_a_3238_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3242_ = v_a_3238_;
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_snd_3240_);
lean_inc(v_fst_3239_);
lean_dec(v_a_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3244_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 4);
lean_ctor_set(v___x_3242_, 1, v_fst_3239_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3246_ = v___x_3242_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_fst_3239_);
v___x_3246_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
double v___x_3247_; uint8_t v___x_3248_; 
v___x_3247_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3248_ = lean_float_beq(v_startTime_3233_, v___x_3247_);
if (v___x_3248_ == 0)
{
v___y_3209_ = v_startTime_3233_;
v___y_3210_ = v_ctx_3227_;
v___y_3211_ = v_collapsed_3235_;
v___y_3212_ = v_children_3230_;
v___y_3213_ = v___x_3236_;
v___y_3214_ = v_stopTime_3234_;
v___y_3215_ = v_snd_3240_;
v___y_3216_ = v___x_3246_;
v___y_3217_ = v_cls_3232_;
goto v___jp_3208_;
}
else
{
if (v___x_3236_ == 0)
{
v___y_3198_ = v_ctx_3227_;
v___y_3199_ = v_collapsed_3235_;
v___y_3200_ = v___x_3236_;
v___y_3201_ = v_children_3230_;
v___y_3202_ = v_cls_3232_;
v_header_3203_ = v___x_3246_;
v___y_3204_ = v_snd_3240_;
goto v___jp_3197_;
}
else
{
v___y_3209_ = v_startTime_3233_;
v___y_3210_ = v_ctx_3227_;
v___y_3211_ = v_collapsed_3235_;
v___y_3212_ = v_children_3230_;
v___y_3213_ = v___x_3236_;
v___y_3214_ = v_stopTime_3234_;
v___y_3215_ = v_snd_3240_;
v___y_3216_ = v___x_3246_;
v___y_3217_ = v_cls_3232_;
goto v___jp_3208_;
}
}
}
}
}
else
{
lean_dec(v_cls_3232_);
lean_dec_ref(v_children_3230_);
lean_dec(v_ctx_3227_);
lean_dec_ref(v_nCtx_3075_);
return v___x_3237_;
}
}
else
{
size_t v_sz_3251_; size_t v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_cls_3232_);
lean_dec_ref(v_header_3229_);
v_sz_3251_ = lean_array_size(v_children_3230_);
v___x_3252_ = ((size_t)0ULL);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3075_, v_ctx_3227_, v_sz_3251_, v___x_3252_, v_children_3230_, v___y_3231_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3272_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3272_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_fst_3258_; lean_object* v_snd_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3271_; 
v_fst_3258_ = lean_ctor_get(v_a_3254_, 0);
v_snd_3259_ = lean_ctor_get(v_a_3254_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_a_3254_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3261_ = v_a_3254_;
v_isShared_3262_ = v_isSharedCheck_3271_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_snd_3259_);
lean_inc(v_fst_3258_);
lean_dec(v_a_3254_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3271_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3263_ = lean_array_to_list(v_fst_3258_);
v___x_3264_ = l_Std_Format_join(v___x_3263_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3264_);
v___x_3266_ = v___x_3261_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_snd_3259_);
v___x_3266_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3266_);
v___x_3268_ = v___x_3256_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3253_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3253_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
v___jp_3281_:
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3282_, v_d_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3324_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3286_);
v_fst_3288_ = lean_ctor_get(v_a_3287_, 0);
v_snd_3289_ = lean_ctor_get(v_a_3287_, 1);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3291_ = v_a_3287_;
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snd_3289_);
lean_inc(v_fst_3288_);
lean_dec(v_a_3287_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 2);
lean_ctor_set(v___x_3291_, 1, v_fst_3288_);
lean_ctor_set(v___x_3291_, 0, v_wi_3283_);
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_wi_3283_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_fst_3288_);
v___x_3294_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3294_, v_snd_3289_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3314_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3314_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3314_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3313_; 
v_fst_3300_ = lean_ctor_get(v_a_3296_, 0);
v_snd_3301_ = lean_ctor_get(v_a_3296_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_a_3296_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3303_ = v_a_3296_;
v_isShared_3304_ = v_isSharedCheck_3313_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_snd_3301_);
lean_inc(v_fst_3300_);
lean_dec(v_a_3296_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3313_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_fst_3300_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3306_);
v___x_3308_ = v___x_3303_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_snd_3301_);
v___x_3308_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; 
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3308_);
v___x_3310_ = v___x_3298_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
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
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
v_a_3315_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3295_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3295_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_wi_3283_);
return v___x_3286_;
}
}
v___jp_3325_:
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v_ctx_3326_);
v_a_3076_ = v___x_3329_;
v_a_3077_ = v_d_3327_;
v_a_3078_ = v___y_3328_;
goto _start;
}
v___jp_3331_:
{
lean_object* v___x_3336_; 
lean_inc(v_ctx_3332_);
lean_inc_ref(v_nCtx_3075_);
v___x_3336_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3332_, v_d_u2081_3333_, v___y_3335_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v_fst_3338_; lean_object* v_snd_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3364_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref(v___x_3336_);
v_fst_3338_ = lean_ctor_get(v_a_3337_, 0);
v_snd_3339_ = lean_ctor_get(v_a_3337_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_a_3337_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3341_ = v_a_3337_;
v_isShared_3342_ = v_isSharedCheck_3364_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_snd_3339_);
lean_inc(v_fst_3338_);
lean_dec(v_a_3337_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3364_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3332_, v_d_u2082_3334_, v_snd_3339_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3363_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3363_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3363_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3362_; 
v_fst_3348_ = lean_ctor_get(v_a_3344_, 0);
v_snd_3349_ = lean_ctor_get(v_a_3344_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_a_3344_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3351_ = v_a_3344_;
v_isShared_3352_ = v_isSharedCheck_3362_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3349_);
lean_inc(v_fst_3348_);
lean_dec(v_a_3344_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3362_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set_tag(v___x_3341_, 5);
lean_ctor_set(v___x_3341_, 1, v_fst_3348_);
v___x_3354_ = v___x_3341_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_fst_3338_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_fst_3348_);
v___x_3354_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3354_);
v___x_3356_ = v___x_3351_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_snd_3349_);
v___x_3356_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3356_);
v___x_3358_ = v___x_3346_;
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
}
}
}
else
{
lean_del_object(v___x_3341_);
lean_dec(v_fst_3338_);
return v___x_3343_;
}
}
}
else
{
lean_dec_ref(v_d_u2082_3334_);
lean_dec(v_ctx_3332_);
lean_dec_ref(v_nCtx_3075_);
return v___x_3336_;
}
}
v___jp_3365_:
{
lean_object* v___x_3369_; 
v___x_3369_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3075_, v_ctx_3366_, v_d_3367_, v___y_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3388_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3388_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3388_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_fst_3374_; lean_object* v_snd_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3387_; 
v_fst_3374_ = lean_ctor_get(v_a_3370_, 0);
v_snd_3375_ = lean_ctor_get(v_a_3370_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_a_3370_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3377_ = v_a_3370_;
v_isShared_3378_ = v_isSharedCheck_3387_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_snd_3375_);
lean_inc(v_fst_3374_);
lean_dec(v_a_3370_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3387_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3379_ = 0;
v___x_3380_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3380_, 0, v_fst_3374_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*1, v___x_3379_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3380_);
v___x_3382_ = v___x_3377_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_snd_3375_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3384_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3382_);
v___x_3384_ = v___x_3372_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
else
{
return v___x_3369_;
}
}
v___jp_3390_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_apply_2(v___y_3391_, v___y_3394_, lean_box(0));
v___x_3396_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_3395_, v___x_3389_);
lean_dec(v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 1)
{
lean_object* v_val_3397_; 
v_val_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_val_3397_);
lean_dec_ref(v___x_3396_);
v_a_3076_ = v___y_3393_;
v_a_3077_ = v_val_3397_;
v_a_3078_ = v___y_3392_;
goto _start;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v___x_3396_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v_nCtx_3075_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6);
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object* v_nCtx_3530_, lean_object* v_ctx_3531_, size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_bs_3534_, lean_object* v___y_3535_){
_start:
{
uint8_t v___x_3537_; 
v___x_3537_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_dec(v_ctx_3531_);
lean_dec_ref(v_nCtx_3530_);
v___x_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3538_, 0, v_bs_3534_);
lean_ctor_set(v___x_3538_, 1, v___y_3535_);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
else
{
lean_object* v_v_3540_; lean_object* v___x_3541_; 
v_v_3540_ = lean_array_uget_borrowed(v_bs_3534_, v_i_3533_);
lean_inc(v_v_3540_);
lean_inc(v_ctx_3531_);
lean_inc_ref(v_nCtx_3530_);
v___x_3541_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3530_, v_ctx_3531_, v_v_3540_, v___y_3535_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___x_3545_; lean_object* v_bs_x27_3546_; size_t v___x_3547_; size_t v___x_3548_; lean_object* v___x_3549_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v_fst_3543_ = lean_ctor_get(v_a_3542_, 0);
lean_inc(v_fst_3543_);
v_snd_3544_ = lean_ctor_get(v_a_3542_, 1);
lean_inc(v_snd_3544_);
lean_dec(v_a_3542_);
v___x_3545_ = lean_unsigned_to_nat(0u);
v_bs_x27_3546_ = lean_array_uset(v_bs_3534_, v_i_3533_, v___x_3545_);
v___x_3547_ = ((size_t)1ULL);
v___x_3548_ = lean_usize_add(v_i_3533_, v___x_3547_);
v___x_3549_ = lean_array_uset(v_bs_x27_3546_, v_i_3533_, v_fst_3543_);
v_i_3533_ = v___x_3548_;
v_bs_3534_ = v___x_3549_;
v___y_3535_ = v_snd_3544_;
goto _start;
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_bs_3534_);
lean_dec(v_ctx_3531_);
lean_dec_ref(v_nCtx_3530_);
v_a_3551_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3541_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3541_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0___boxed(lean_object* v_nCtx_3559_, lean_object* v_ctx_3560_, lean_object* v_sz_3561_, lean_object* v_i_3562_, lean_object* v_bs_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
size_t v_sz_boxed_3566_; size_t v_i_boxed_3567_; lean_object* v_res_3568_; 
v_sz_boxed_3566_ = lean_unbox_usize(v_sz_3561_);
lean_dec(v_sz_3561_);
v_i_boxed_3567_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3559_, v_ctx_3560_, v_sz_boxed_3566_, v_i_boxed_3567_, v_bs_3563_, v___y_3564_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object* v_nCtx_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object* v_msgData_3580_){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3582_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0));
v___x_3583_ = lean_box(0);
v___x_3584_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1));
v___x_3585_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v___x_3582_, v___x_3583_, v_msgData_3580_, v___x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object* v_msgData_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3586_);
return v_res_3588_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object* v_g_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_Widget_goalToInteractive(v_g_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3607_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3607_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3607_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3601_, 0, v_a_3597_);
v___x_3602_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
v___x_3603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3603_);
v___x_3605_ = v___x_3599_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
v_a_3608_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3596_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3596_);
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object* v_g_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(v_g_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object* v_f_3623_, size_t v_sz_3624_, size_t v_i_3625_, lean_object* v_bs_3626_){
_start:
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_usize_dec_lt(v_i_3625_, v_sz_3624_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
lean_dec_ref(v_f_3623_);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v_bs_3626_);
return v___x_3629_;
}
else
{
lean_object* v_v_3630_; lean_object* v___x_3631_; 
v_v_3630_ = lean_array_uget_borrowed(v_bs_3626_, v_i_3625_);
lean_inc(v_v_3630_);
lean_inc_ref(v_f_3623_);
v___x_3631_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3623_, v_v_3630_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v_bs_x27_3634_; size_t v___x_3635_; size_t v___x_3636_; lean_object* v___x_3637_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref(v___x_3631_);
v___x_3633_ = lean_unsigned_to_nat(0u);
v_bs_x27_3634_ = lean_array_uset(v_bs_3626_, v_i_3625_, v___x_3633_);
v___x_3635_ = ((size_t)1ULL);
v___x_3636_ = lean_usize_add(v_i_3625_, v___x_3635_);
v___x_3637_ = lean_array_uset(v_bs_x27_3634_, v_i_3625_, v_a_3632_);
v_i_3625_ = v___x_3636_;
v_bs_3626_ = v___x_3637_;
goto _start;
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_bs_3626_);
lean_dec_ref(v_f_3623_);
v_a_3639_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3631_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3631_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object* v_f_3647_, lean_object* v_x_3648_){
_start:
{
switch(lean_obj_tag(v_x_3648_))
{
case 0:
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v_f_3647_);
v_a_3650_ = lean_ctor_get(v_x_3648_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3652_ = v_x_3648_;
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v_x_3648_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
}
case 1:
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3685_; 
v_a_3659_ = lean_ctor_get(v_x_3648_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3661_ = v_x_3648_;
v_isShared_3662_ = v_isSharedCheck_3685_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v_x_3648_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3685_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
size_t v_sz_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v_sz_3663_ = lean_array_size(v_a_3659_);
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3647_, v_sz_3663_, v___x_3664_, v_a_3659_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3676_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v_a_3666_);
v___x_3671_ = v___x_3661_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3671_);
v___x_3673_ = v___x_3668_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_del_object(v___x_3661_);
v_a_3677_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3665_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3665_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
default: 
{
lean_object* v_a_3686_; lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3686_ = lean_ctor_get(v_x_3648_, 0);
lean_inc(v_a_3686_);
v_a_3687_ = lean_ctor_get(v_x_3648_, 1);
lean_inc_ref(v_a_3687_);
lean_dec_ref(v_x_3648_);
v___x_3688_ = lean_apply_3(v_f_3647_, v_a_3686_, v_a_3687_, lean_box(0));
return v___x_3688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg___boxed(lean_object* v_f_3689_, lean_object* v_x_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3689_, v_x_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object* v_f_3693_, lean_object* v_sz_3694_, lean_object* v_i_3695_, lean_object* v_bs_3696_, lean_object* v___y_3697_){
_start:
{
size_t v_sz_boxed_3698_; size_t v_i_boxed_3699_; lean_object* v_res_3700_; 
v_sz_boxed_3698_ = lean_unbox_usize(v_sz_3694_);
lean_dec(v_sz_3694_);
v_i_boxed_3699_ = lean_unbox_usize(v_i_3695_);
lean_dec(v_i_3695_);
v_res_3700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3693_, v_sz_boxed_3698_, v_i_boxed_3699_, v_bs_3696_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t v_sz_3701_, size_t v_i_3702_, lean_object* v_bs_3703_){
_start:
{
uint8_t v___x_3705_; 
v___x_3705_ = lean_usize_dec_lt(v_i_3702_, v_sz_3701_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_bs_3703_);
return v___x_3706_;
}
else
{
lean_object* v_v_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_bs_x27_3710_; size_t v___x_3711_; size_t v___x_3712_; lean_object* v___x_3713_; 
v_v_3707_ = lean_array_uget_borrowed(v_bs_3703_, v_i_3702_);
lean_inc(v_v_3707_);
v___x_3708_ = l_Lean_Server_WithRpcRef_mk___redArg(v_v_3707_);
v___x_3709_ = lean_unsigned_to_nat(0u);
v_bs_x27_3710_ = lean_array_uset(v_bs_3703_, v_i_3702_, v___x_3709_);
v___x_3711_ = ((size_t)1ULL);
v___x_3712_ = lean_usize_add(v_i_3702_, v___x_3711_);
v___x_3713_ = lean_array_uset(v_bs_x27_3710_, v_i_3702_, v___x_3708_);
v_i_3702_ = v___x_3712_;
v_bs_3703_ = v___x_3713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object* v_sz_3715_, lean_object* v_i_3716_, lean_object* v_bs_3717_, lean_object* v___y_3718_){
_start:
{
size_t v_sz_boxed_3719_; size_t v_i_boxed_3720_; lean_object* v_res_3721_; 
v_sz_boxed_3719_ = lean_unbox_usize(v_sz_3715_);
lean_dec(v_sz_3715_);
v_i_boxed_3720_ = lean_unbox_usize(v_i_3716_);
lean_dec(v_i_3716_);
v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_boxed_3719_, v_i_boxed_3720_, v_bs_3717_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object* v_col_3722_, lean_object* v_embeds_3723_, size_t v_sz_3724_, size_t v_i_3725_, lean_object* v_bs_3726_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_usize_dec_lt(v_i_3725_, v_sz_3724_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec_ref(v_embeds_3723_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_bs_3726_);
return v___x_3729_;
}
else
{
lean_object* v_v_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_v_3730_ = lean_array_uget_borrowed(v_bs_3726_, v_i_3725_);
v___x_3731_ = lean_unsigned_to_nat(2u);
v___x_3732_ = lean_nat_add(v_col_3722_, v___x_3731_);
lean_inc(v_v_3730_);
lean_inc_ref(v_embeds_3723_);
v___x_3733_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3723_, v_v_3730_, v___x_3732_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v_bs_x27_3736_; size_t v___x_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = lean_unsigned_to_nat(0u);
v_bs_x27_3736_ = lean_array_uset(v_bs_3726_, v_i_3725_, v___x_3735_);
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3725_, v___x_3737_);
v___x_3739_ = lean_array_uset(v_bs_x27_3736_, v_i_3725_, v_a_3734_);
v_i_3725_ = v___x_3738_;
v_bs_3726_ = v___x_3739_;
goto _start;
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_bs_3726_);
lean_dec_ref(v_embeds_3723_);
v_a_3741_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3733_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3733_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object* v___x_3749_, lean_object* v_embeds_3750_, lean_object* v_indent_3751_, lean_object* v_x_3752_, lean_object* v_tt_3753_){
_start:
{
lean_object* v_fst_3755_; lean_object* v_snd_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3869_; 
v_fst_3755_ = lean_ctor_get(v_x_3752_, 0);
v_snd_3756_ = lean_ctor_get(v_x_3752_, 1);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_x_3752_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3758_ = v_x_3752_;
v_isShared_3759_ = v_isSharedCheck_3869_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_snd_3756_);
lean_inc(v_fst_3755_);
lean_dec(v_x_3752_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3869_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_array_get(v___x_3749_, v_embeds_3750_, v_fst_3755_);
lean_dec(v_fst_3755_);
switch(lean_obj_tag(v___x_3760_))
{
case 0:
{
lean_object* v_ctx_3761_; lean_object* v_infos_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3758_);
lean_dec(v_snd_3756_);
lean_dec(v_indent_3751_);
lean_dec_ref(v_embeds_3750_);
v_ctx_3761_ = lean_ctor_get(v___x_3760_, 0);
v_infos_3762_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3764_ = v___x_3760_;
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_infos_3762_);
lean_inc(v_ctx_3761_);
lean_dec(v___x_3760_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3766_ = l_Lean_Widget_tagCodeInfos(v_ctx_3761_, v_infos_3762_, v_tt_3753_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
v___x_3768_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3765_ == 0)
{
lean_ctor_set_tag(v___x_3764_, 2);
lean_ctor_set(v___x_3764_, 1, v___x_3768_);
lean_ctor_set(v___x_3764_, 0, v___x_3767_);
v___x_3770_ = v___x_3764_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
}
}
case 1:
{
lean_object* v_ctx_3774_; lean_object* v_lctx_3775_; lean_object* v_g_3776_; lean_object* v___f_3777_; lean_object* v___x_3778_; 
lean_del_object(v___x_3758_);
lean_dec(v_snd_3756_);
lean_dec_ref(v_tt_3753_);
lean_dec(v_indent_3751_);
lean_dec_ref(v_embeds_3750_);
v_ctx_3774_ = lean_ctor_get(v___x_3760_, 0);
lean_inc_ref(v_ctx_3774_);
v_lctx_3775_ = lean_ctor_get(v___x_3760_, 1);
lean_inc_ref(v_lctx_3775_);
v_g_3776_ = lean_ctor_get(v___x_3760_, 2);
lean_inc(v_g_3776_);
lean_dec_ref(v___x_3760_);
v___f_3777_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3777_, 0, v_g_3776_);
v___x_3778_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_3774_, v_lctx_3775_, v___f_3777_);
return v___x_3778_;
}
case 2:
{
lean_object* v_wi_3779_; lean_object* v_alt_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v_tt_3753_);
lean_dec(v_indent_3751_);
v_wi_3779_ = lean_ctor_get(v___x_3760_, 0);
v_alt_3780_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3782_ = v___x_3760_;
v_isShared_3783_ = v_isSharedCheck_3800_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_alt_3780_);
lean_inc(v_wi_3779_);
lean_dec(v___x_3760_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3800_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; 
v___x_3784_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3750_, v_alt_3780_, v_snd_3756_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3799_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v_a_3785_);
v___x_3790_ = v___x_3782_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_wi_3779_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3791_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 2);
lean_ctor_set(v___x_3758_, 1, v___x_3791_);
lean_ctor_set(v___x_3758_, 0, v___x_3790_);
v___x_3793_ = v___x_3758_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3793_);
v___x_3795_ = v___x_3787_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
else
{
lean_del_object(v___x_3782_);
lean_dec_ref(v_wi_3779_);
lean_del_object(v___x_3758_);
return v___x_3784_;
}
}
}
case 3:
{
lean_object* v_cls_3801_; lean_object* v_msg_3802_; uint8_t v_collapsed_3803_; lean_object* v_children_3804_; lean_object* v_col_3805_; lean_object* v_children_3807_; 
lean_dec_ref(v_tt_3753_);
v_cls_3801_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_cls_3801_);
v_msg_3802_ = lean_ctor_get(v___x_3760_, 1);
lean_inc(v_msg_3802_);
v_collapsed_3803_ = lean_ctor_get_uint8(v___x_3760_, sizeof(void*)*3);
v_children_3804_ = lean_ctor_get(v___x_3760_, 2);
lean_inc_ref(v_children_3804_);
lean_dec_ref(v___x_3760_);
v_col_3805_ = lean_nat_add(v_indent_3751_, v_snd_3756_);
lean_dec(v_snd_3756_);
if (lean_obj_tag(v_children_3804_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3841_; 
v_a_3822_ = lean_ctor_get(v_children_3804_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_children_3804_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3824_ = v_children_3804_;
v_isShared_3825_ = v_isSharedCheck_3841_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v_children_3804_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3841_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v_sz_3826_ = lean_array_size(v_a_3822_);
v___x_3827_ = ((size_t)0ULL);
lean_inc_ref(v_embeds_3750_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3805_, v_embeds_3750_, v_sz_3826_, v___x_3827_, v_a_3822_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_a_3829_);
v___x_3831_ = v___x_3824_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
v_children_3807_ = v___x_3831_;
goto v___jp_3806_;
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_del_object(v___x_3824_);
lean_dec(v_col_3805_);
lean_dec(v_msg_3802_);
lean_dec(v_cls_3801_);
lean_del_object(v___x_3758_);
lean_dec(v_indent_3751_);
lean_dec_ref(v_embeds_3750_);
v_a_3833_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3828_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3828_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3865_; 
v_a_3842_ = lean_ctor_get(v_children_3804_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_children_3804_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3844_ = v_children_3804_;
v_isShared_3845_ = v_isSharedCheck_3865_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v_children_3804_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3865_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
size_t v_sz_3846_; size_t v___x_3847_; lean_object* v___x_3848_; 
v_sz_3846_ = lean_array_size(v_a_3842_);
v___x_3847_ = ((size_t)0ULL);
v___x_3848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_3846_, v___x_3847_, v_a_3842_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3855_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = lean_unsigned_to_nat(2u);
v___x_3851_ = lean_nat_add(v_col_3805_, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
lean_ctor_set(v___x_3852_, 1, v_a_3849_);
v___x_3853_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_3852_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3853_);
v___x_3855_ = v___x_3844_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
v_children_3807_ = v___x_3855_;
goto v___jp_3806_;
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_del_object(v___x_3844_);
lean_dec(v_col_3805_);
lean_dec(v_msg_3802_);
lean_dec(v_cls_3801_);
lean_del_object(v___x_3758_);
lean_dec(v_indent_3751_);
lean_dec_ref(v_embeds_3750_);
v_a_3857_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3848_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3848_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
v___jp_3806_:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3750_, v_msg_3802_, v_col_3805_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3821_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3821_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3821_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3813_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_3813_, 0, v_indent_3751_);
lean_ctor_set(v___x_3813_, 1, v_cls_3801_);
lean_ctor_set(v___x_3813_, 2, v_a_3809_);
lean_ctor_set(v___x_3813_, 3, v_children_3807_);
lean_ctor_set_uint8(v___x_3813_, sizeof(void*)*4, v_collapsed_3803_);
v___x_3814_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 2);
lean_ctor_set(v___x_3758_, 1, v___x_3814_);
lean_ctor_set(v___x_3758_, 0, v___x_3813_);
v___x_3816_ = v___x_3758_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3818_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3816_);
v___x_3818_ = v___x_3811_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_dec_ref(v_children_3807_);
lean_dec(v_cls_3801_);
lean_del_object(v___x_3758_);
lean_dec(v_indent_3751_);
return v___x_3808_;
}
}
}
default: 
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_del_object(v___x_3758_);
lean_dec(v_snd_3756_);
lean_dec(v_indent_3751_);
lean_dec_ref(v_embeds_3750_);
v___x_3866_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3753_);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed(lean_object* v___x_3870_, lean_object* v_embeds_3871_, lean_object* v_indent_3872_, lean_object* v_x_3873_, lean_object* v_tt_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(v___x_3870_, v_embeds_3871_, v_indent_3872_, v_x_3873_, v_tt_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(lean_object* v_embeds_3877_, lean_object* v_fmt_3878_, lean_object* v_indent_3879_){
_start:
{
lean_object* v___x_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3881_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default;
lean_inc(v_indent_3879_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3882_, 0, v___x_3881_);
lean_closure_set(v___f_3882_, 1, v_embeds_3877_);
lean_closure_set(v___f_3882_, 2, v_indent_3879_);
v___x_3883_ = l_Std_Format_defWidth;
v___x_3884_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_3878_, v_indent_3879_, v___x_3883_);
v___x_3885_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v___f_3882_, v___x_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___boxed(lean_object* v_embeds_3886_, lean_object* v_fmt_3887_, lean_object* v_indent_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3886_, v_fmt_3887_, v_indent_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object* v_col_3891_, lean_object* v_embeds_3892_, lean_object* v_sz_3893_, lean_object* v_i_3894_, lean_object* v_bs_3895_, lean_object* v___y_3896_){
_start:
{
size_t v_sz_boxed_3897_; size_t v_i_boxed_3898_; lean_object* v_res_3899_; 
v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3893_);
lean_dec(v_sz_3893_);
v_i_boxed_3898_ = lean_unbox_usize(v_i_3894_);
lean_dec(v_i_3894_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3891_, v_embeds_3892_, v_sz_boxed_3897_, v_i_boxed_3898_, v_bs_3895_);
lean_dec(v_col_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object* v_00_u03b1_3900_, lean_object* v_00_u03b2_3901_, lean_object* v_f_3902_, lean_object* v_x_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3902_, v_x_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___boxed(lean_object* v_00_u03b1_3906_, lean_object* v_00_u03b2_3907_, lean_object* v_f_3908_, lean_object* v_x_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(v_00_u03b1_3906_, v_00_u03b2_3907_, v_f_3908_, v_x_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object* v_00_u03b1_3912_, lean_object* v_00_u03b2_3913_, lean_object* v_f_3914_, size_t v_sz_3915_, size_t v_i_3916_, lean_object* v_bs_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3914_, v_sz_3915_, v_i_3916_, v_bs_3917_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3920_, lean_object* v_00_u03b2_3921_, lean_object* v_f_3922_, lean_object* v_sz_3923_, lean_object* v_i_3924_, lean_object* v_bs_3925_, lean_object* v___y_3926_){
_start:
{
size_t v_sz_boxed_3927_; size_t v_i_boxed_3928_; lean_object* v_res_3929_; 
v_sz_boxed_3927_ = lean_unbox_usize(v_sz_3923_);
lean_dec(v_sz_3923_);
v_i_boxed_3928_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_res_3929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(v_00_u03b1_3920_, v_00_u03b2_3921_, v_f_3922_, v_sz_boxed_3927_, v_i_boxed_3928_, v_bs_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object* v_x_3930_, lean_object* v_tt_3931_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3931_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object* v_x_3934_, lean_object* v_tt_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_Widget_msgToInteractive___lam__0(v_x_3934_, v_tt_3935_);
lean_dec_ref(v_x_3934_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object* v_msgData_3938_, uint8_t v_hasWidgets_3939_, lean_object* v_indent_3940_){
_start:
{
if (v_hasWidgets_3939_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___f_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_indent_3940_);
v___x_3942_ = lean_box(0);
v___x_3943_ = l_Lean_MessageData_format(v_msgData_3938_, v___x_3942_);
v___f_3944_ = ((lean_object*)(l_Lean_Widget_msgToInteractive___closed__0));
v___x_3945_ = lean_unsigned_to_nat(0u);
v___x_3946_ = l_Std_Format_defWidth;
v___x_3947_ = l_Lean_Widget_TaggedText_prettyTagged(v___x_3943_, v___x_3945_, v___x_3946_);
v___x_3948_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_3944_, v___x_3947_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3938_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___x_3954_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref(v___x_3950_);
v_fst_3952_ = lean_ctor_get(v_a_3951_, 0);
lean_inc(v_fst_3952_);
v_snd_3953_ = lean_ctor_get(v_a_3951_, 1);
lean_inc(v_snd_3953_);
lean_dec(v_a_3951_);
v___x_3954_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_snd_3953_, v_fst_3952_, v_indent_3940_);
return v___x_3954_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_indent_3940_);
v_a_3955_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3950_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3950_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object* v_msgData_3963_, lean_object* v_hasWidgets_3964_, lean_object* v_indent_3965_, lean_object* v_a_3966_){
_start:
{
uint8_t v_hasWidgets_boxed_3967_; lean_object* v_res_3968_; 
v_hasWidgets_boxed_3967_ = lean_unbox(v_hasWidgets_3964_);
v_res_3968_ = l_Lean_Widget_msgToInteractive(v_msgData_3963_, v_hasWidgets_boxed_3967_, v_indent_3965_);
return v_res_3968_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object* v_x_3972_){
_start:
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1));
v___x_3974_ = lean_name_eq(v_x_3972_, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object* v_x_3975_){
_start:
{
uint8_t v_res_3976_; lean_object* v_r_3977_; 
v_res_3976_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(v_x_3975_);
lean_dec(v_x_3975_);
v_r_3977_ = lean_box(v_res_3976_);
return v_r_3977_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object* v_x_3983_){
_start:
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2));
v___x_3985_ = lean_name_eq(v_x_3983_, v___x_3984_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object* v_x_3986_){
_start:
{
uint8_t v_res_3987_; lean_object* v_r_3988_; 
v_res_3987_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(v_x_3986_);
lean_dec(v_x_3986_);
v_r_3988_ = lean_box(v_res_3987_);
return v_r_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object* v_text_4027_, lean_object* v_m_4028_, uint8_t v_hasWidgets_4029_){
_start:
{
lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v_pos_4044_; lean_object* v_endPos_4045_; uint8_t v_keepFullRange_4046_; uint8_t v_severity_4047_; uint8_t v_isSilent_4048_; lean_object* v_data_4049_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___f_4098_; lean_object* v___f_4099_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4126_; lean_object* v___y_4127_; uint8_t v___y_4128_; lean_object* v_low_4134_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4148_; 
v_pos_4044_ = lean_ctor_get(v_m_4028_, 1);
lean_inc_ref(v_pos_4044_);
v_endPos_4045_ = lean_ctor_get(v_m_4028_, 2);
lean_inc(v_endPos_4045_);
v_keepFullRange_4046_ = lean_ctor_get_uint8(v_m_4028_, sizeof(void*)*5);
v_severity_4047_ = lean_ctor_get_uint8(v_m_4028_, sizeof(void*)*5 + 1);
v_isSilent_4048_ = lean_ctor_get_uint8(v_m_4028_, sizeof(void*)*5 + 2);
v_data_4049_ = lean_ctor_get(v_m_4028_, 4);
lean_inc(v_data_4049_);
lean_dec_ref(v_m_4028_);
v___f_4098_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__2));
v___f_4099_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__3));
lean_inc_ref(v_pos_4044_);
lean_inc_ref(v_text_4027_);
v_low_4134_ = l_Lean_FileMap_leanPosToLspPos(v_text_4027_, v_pos_4044_);
if (lean_obj_tag(v_endPos_4045_) == 0)
{
lean_inc_ref(v_pos_4044_);
v___y_4148_ = v_pos_4044_;
goto v___jp_4147_;
}
else
{
lean_object* v_val_4168_; 
v_val_4168_ = lean_ctor_get(v_endPos_4045_, 0);
lean_inc(v_val_4168_);
v___y_4148_ = v_val_4168_;
goto v___jp_4147_;
}
v___jp_4031_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___y_4032_);
v___x_4042_ = lean_box(0);
v___x_4043_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4043_, 0, v___y_4038_);
lean_ctor_set(v___x_4043_, 1, v___x_4041_);
lean_ctor_set(v___x_4043_, 2, v___y_4034_);
lean_ctor_set(v___x_4043_, 3, v___y_4033_);
lean_ctor_set(v___x_4043_, 4, v___y_4040_);
lean_ctor_set(v___x_4043_, 5, v___y_4037_);
lean_ctor_set(v___x_4043_, 6, v___y_4036_);
lean_ctor_set(v___x_4043_, 7, v___y_4039_);
lean_ctor_set(v___x_4043_, 8, v___y_4035_);
lean_ctor_set(v___x_4043_, 9, v___x_4042_);
lean_ctor_set(v___x_4043_, 10, v___x_4042_);
return v___x_4043_;
}
v___jp_4050_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = l_Lean_MessageData_kind(v_data_4049_);
lean_dec(v_data_4049_);
v___x_4061_ = l_Lean_errorNameOfKind_x3f(v___x_4060_);
lean_dec(v___x_4060_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_box(0);
v___y_4032_ = v___y_4051_;
v___y_4033_ = v___y_4052_;
v___y_4034_ = v___y_4053_;
v___y_4035_ = v___y_4054_;
v___y_4036_ = v___y_4059_;
v___y_4037_ = v___y_4056_;
v___y_4038_ = v___y_4057_;
v___y_4039_ = v___y_4058_;
v___y_4040_ = v___x_4062_;
goto v___jp_4031_;
}
else
{
lean_object* v_val_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4072_; 
v_val_4063_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4065_ = v___x_4061_;
v_isShared_4066_ = v_isSharedCheck_4072_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_val_4063_);
lean_dec(v___x_4061_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4072_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4067_ = l_Lean_Name_toString(v_val_4063_, v___y_4055_);
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 0, v___x_4068_);
v___x_4070_ = v___x_4065_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
v___y_4032_ = v___y_4051_;
v___y_4033_ = v___y_4052_;
v___y_4034_ = v___y_4053_;
v___y_4035_ = v___y_4054_;
v___y_4036_ = v___y_4059_;
v___y_4037_ = v___y_4056_;
v___y_4038_ = v___y_4057_;
v___y_4039_ = v___y_4058_;
v___y_4040_ = v___x_4070_;
goto v___jp_4031_;
}
}
}
}
v___jp_4073_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = lean_unsigned_to_nat(0u);
lean_inc(v_data_4049_);
v___x_4083_ = l_Lean_Widget_msgToInteractive(v_data_4049_, v_hasWidgets_4029_, v___x_4082_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4083_);
v___y_4051_ = v___y_4074_;
v___y_4052_ = v___y_4075_;
v___y_4053_ = v___y_4076_;
v___y_4054_ = v___y_4081_;
v___y_4055_ = v___y_4077_;
v___y_4056_ = v___y_4078_;
v___y_4057_ = v___y_4079_;
v___y_4058_ = v___y_4080_;
v___y_4059_ = v_a_4084_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4097_; 
v_a_4085_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4087_ = v___x_4083_;
v_isShared_4088_ = v_isSharedCheck_4097_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4083_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4097_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4089_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__0));
v___x_4090_ = lean_io_error_to_string(v_a_4085_);
v___x_4091_ = lean_string_append(v___x_4089_, v___x_4090_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__1));
v___x_4093_ = lean_string_append(v___x_4091_, v___x_4092_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4093_);
v___x_4095_ = v___x_4087_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
v___y_4051_ = v___y_4074_;
v___y_4052_ = v___y_4075_;
v___y_4053_ = v___y_4076_;
v___y_4054_ = v___y_4081_;
v___y_4055_ = v___y_4077_;
v___y_4056_ = v___y_4078_;
v___y_4057_ = v___y_4079_;
v___y_4058_ = v___y_4080_;
v___y_4059_ = v___x_4095_;
goto v___jp_4050_;
}
}
}
}
v___jp_4100_:
{
uint8_t v___x_4108_; 
lean_inc(v_data_4049_);
v___x_4108_ = l_Lean_MessageData_hasTag(v___f_4099_, v_data_4049_);
if (v___x_4108_ == 0)
{
uint8_t v___x_4109_; 
lean_inc(v_data_4049_);
v___x_4109_ = l_Lean_MessageData_hasTag(v___f_4098_, v_data_4049_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_box(0);
v___y_4074_ = v___y_4101_;
v___y_4075_ = v___y_4102_;
v___y_4076_ = v___y_4103_;
v___y_4077_ = v___y_4104_;
v___y_4078_ = v___y_4105_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4107_;
v___y_4081_ = v___x_4110_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4111_; 
v___x_4111_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__5));
v___y_4074_ = v___y_4101_;
v___y_4075_ = v___y_4102_;
v___y_4076_ = v___y_4103_;
v___y_4077_ = v___y_4104_;
v___y_4078_ = v___y_4105_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4107_;
v___y_4081_ = v___x_4111_;
goto v___jp_4073_;
}
}
else
{
lean_object* v___x_4112_; 
v___x_4112_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__7));
v___y_4074_ = v___y_4101_;
v___y_4075_ = v___y_4102_;
v___y_4076_ = v___y_4103_;
v___y_4077_ = v___y_4104_;
v___y_4078_ = v___y_4105_;
v___y_4079_ = v___y_4106_;
v___y_4080_ = v___y_4107_;
v___y_4081_ = v___x_4112_;
goto v___jp_4073_;
}
}
v___jp_4113_:
{
lean_object* v_source_x3f_4119_; uint8_t v___x_4120_; 
v_source_x3f_4119_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__9));
lean_inc(v_data_4049_);
v___x_4120_ = l_Lean_MessageData_isDeprecationWarning(v_data_4049_);
if (v___x_4120_ == 0)
{
uint8_t v___x_4121_; 
lean_inc(v_data_4049_);
v___x_4121_ = l_Lean_MessageData_isUnusedVariableWarning(v_data_4049_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_box(0);
v___y_4101_ = v___y_4114_;
v___y_4102_ = v___y_4118_;
v___y_4103_ = v___y_4115_;
v___y_4104_ = v___y_4116_;
v___y_4105_ = v_source_x3f_4119_;
v___y_4106_ = v___y_4117_;
v___y_4107_ = v___x_4122_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__11));
v___y_4101_ = v___y_4114_;
v___y_4102_ = v___y_4118_;
v___y_4103_ = v___y_4115_;
v___y_4104_ = v___y_4116_;
v___y_4105_ = v_source_x3f_4119_;
v___y_4106_ = v___y_4117_;
v___y_4107_ = v___x_4123_;
goto v___jp_4100_;
}
}
else
{
lean_object* v___x_4124_; 
v___x_4124_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__13));
v___y_4101_ = v___y_4114_;
v___y_4102_ = v___y_4118_;
v___y_4103_ = v___y_4115_;
v___y_4104_ = v___y_4116_;
v___y_4105_ = v_source_x3f_4119_;
v___y_4106_ = v___y_4117_;
v___y_4107_ = v___x_4124_;
goto v___jp_4100_;
}
}
v___jp_4125_:
{
lean_object* v___x_4129_; lean_object* v_severity_x3f_4130_; uint8_t v___x_4131_; 
v___x_4129_ = lean_box(v___y_4128_);
v_severity_x3f_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_severity_x3f_4130_, 0, v___x_4129_);
v___x_4131_ = 1;
if (v_isSilent_4048_ == 0)
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_box(0);
v___y_4114_ = v___y_4126_;
v___y_4115_ = v_severity_x3f_4130_;
v___y_4116_ = v___x_4131_;
v___y_4117_ = v___y_4127_;
v___y_4118_ = v___x_4132_;
goto v___jp_4113_;
}
else
{
lean_object* v___x_4133_; 
v___x_4133_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__14));
v___y_4114_ = v___y_4126_;
v___y_4115_ = v_severity_x3f_4130_;
v___y_4116_ = v___x_4131_;
v___y_4117_ = v___y_4127_;
v___y_4118_ = v___x_4133_;
goto v___jp_4113_;
}
}
v___jp_4135_:
{
lean_object* v_range_4138_; lean_object* v_fullRange_4139_; 
lean_inc_ref(v_low_4134_);
v_range_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_4138_, 0, v_low_4134_);
lean_ctor_set(v_range_4138_, 1, v___y_4137_);
v_fullRange_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_fullRange_4139_, 0, v_low_4134_);
lean_ctor_set(v_fullRange_4139_, 1, v___y_4136_);
switch(v_severity_4047_)
{
case 0:
{
uint8_t v___x_4140_; 
v___x_4140_ = 2;
v___y_4126_ = v_fullRange_4139_;
v___y_4127_ = v_range_4138_;
v___y_4128_ = v___x_4140_;
goto v___jp_4125_;
}
case 1:
{
uint8_t v___x_4141_; 
v___x_4141_ = 1;
v___y_4126_ = v_fullRange_4139_;
v___y_4127_ = v_range_4138_;
v___y_4128_ = v___x_4141_;
goto v___jp_4125_;
}
default: 
{
uint8_t v___x_4142_; 
v___x_4142_ = 0;
v___y_4126_ = v_fullRange_4139_;
v___y_4127_ = v_range_4138_;
v___y_4128_ = v___x_4142_;
goto v___jp_4125_;
}
}
}
v___jp_4143_:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_FileMap_leanPosToLspPos(v_text_4027_, v___y_4144_);
v___y_4136_ = v___y_4145_;
v___y_4137_ = v___x_4146_;
goto v___jp_4135_;
}
v___jp_4147_:
{
lean_object* v_fullHigh_4149_; 
lean_inc_ref(v_text_4027_);
v_fullHigh_4149_ = l_Lean_FileMap_leanPosToLspPos(v_text_4027_, v___y_4148_);
if (lean_obj_tag(v_endPos_4045_) == 0)
{
lean_dec_ref(v_pos_4044_);
lean_dec_ref(v_text_4027_);
lean_inc_ref(v_low_4134_);
v___y_4136_ = v_fullHigh_4149_;
v___y_4137_ = v_low_4134_;
goto v___jp_4135_;
}
else
{
if (v_keepFullRange_4046_ == 0)
{
lean_object* v_val_4150_; lean_object* v_line_4151_; lean_object* v_line_4152_; uint8_t v___x_4153_; 
v_val_4150_ = lean_ctor_get(v_endPos_4045_, 0);
lean_inc(v_val_4150_);
lean_dec_ref(v_endPos_4045_);
v_line_4151_ = lean_ctor_get(v_pos_4044_, 0);
lean_inc(v_line_4151_);
lean_dec_ref(v_pos_4044_);
v_line_4152_ = lean_ctor_get(v_val_4150_, 0);
v___x_4153_ = lean_nat_dec_lt(v_line_4151_, v_line_4152_);
if (v___x_4153_ == 0)
{
lean_dec(v_line_4151_);
v___y_4144_ = v_val_4150_;
v___y_4145_ = v_fullHigh_4149_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4164_; 
v_isSharedCheck_4164_ = !lean_is_exclusive(v_val_4150_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; lean_object* v_unused_4166_; 
v_unused_4165_ = lean_ctor_get(v_val_4150_, 1);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_val_4150_, 0);
lean_dec(v_unused_4166_);
v___x_4155_ = v_val_4150_;
v_isShared_4156_ = v_isSharedCheck_4164_;
goto v_resetjp_4154_;
}
else
{
lean_dec(v_val_4150_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4164_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = lean_nat_add(v_line_4151_, v___x_4157_);
lean_dec(v_line_4151_);
v___x_4159_ = lean_unsigned_to_nat(0u);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 1, v___x_4159_);
lean_ctor_set(v___x_4155_, 0, v___x_4158_);
v___x_4161_ = v___x_4155_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4158_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Lean_FileMap_leanPosToLspPos(v_text_4027_, v___x_4161_);
v___y_4136_ = v_fullHigh_4149_;
v___y_4137_ = v___x_4162_;
goto v___jp_4135_;
}
}
}
}
else
{
lean_object* v_val_4167_; 
lean_dec_ref(v_pos_4044_);
v_val_4167_ = lean_ctor_get(v_endPos_4045_, 0);
lean_inc(v_val_4167_);
lean_dec_ref(v_endPos_4045_);
v___y_4144_ = v_val_4167_;
v___y_4145_ = v_fullHigh_4149_;
goto v___jp_4143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object* v_text_4169_, lean_object* v_m_4170_, lean_object* v_hasWidgets_4171_, lean_object* v_a_4172_){
_start:
{
uint8_t v_hasWidgets_boxed_4173_; lean_object* v_res_4174_; 
v_hasWidgets_boxed_4173_ = lean_unbox(v_hasWidgets_4171_);
v_res_4174_ = l_Lean_Widget_msgToInteractiveDiagnostic(v_text_4169_, v_m_4170_, v_hasWidgets_boxed_4173_);
return v_res_4174_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_InteractiveGoal(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default = _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default();
lean_mark_persistent(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_instInhabitedEmbedFmt_default);
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
