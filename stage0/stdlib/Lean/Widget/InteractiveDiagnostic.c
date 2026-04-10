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
extern lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instInhabitedStrictOrLazy_default(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v_inst_58_);
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
lean_inc_ref(v_a_246_);
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
lean_inc_ref(v_a_246_);
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_j_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_309_, v_inst_310_, v_j_311_, v_a_312_);
lean_dec_ref(v_a_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_j_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_inst_316_, v_inst_317_, v_j_318_, v_a_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_j_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_(v_00_u03b1_321_, v_00_u03b2_322_, v_inst_323_, v_inst_324_, v_j_325_, v_a_326_);
lean_dec_ref(v_a_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(lean_object* v_inst_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc_ref(v_inst_329_);
lean_inc_ref(v_inst_328_);
v___x_330_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1_), 6, 4);
lean_closure_set(v___x_330_, 0, lean_box(0));
lean_closure_set(v___x_330_, 1, lean_box(0));
lean_closure_set(v___x_330_, 2, v_inst_328_);
lean_closure_set(v___x_330_, 3, v_inst_329_);
v___x_331_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____boxed), 6, 4);
lean_closure_set(v___x_331_, 0, lean_box(0));
lean_closure_set(v___x_331_, 1, lean_box(0));
lean_closure_set(v___x_331_, 2, v_inst_328_);
lean_closure_set(v___x_331_, 3, v_inst_329_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_inst_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Widget_instRpcEncodableStrictOrLazy___redArg(v_inst_335_, v_inst_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx(lean_object* v_x_347_){
_start:
{
switch(lean_obj_tag(v_x_347_))
{
case 0:
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
return v___x_348_;
}
case 1:
{
lean_object* v___x_349_; 
v___x_349_ = lean_unsigned_to_nat(1u);
return v___x_349_;
}
case 2:
{
lean_object* v___x_350_; 
v___x_350_ = lean_unsigned_to_nat(2u);
return v___x_350_;
}
default: 
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(3u);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorIdx___boxed(lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Widget_MsgEmbed_ctorIdx(v_x_352_);
lean_dec_ref(v_x_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___redArg(lean_object* v_t_354_, lean_object* v_k_355_){
_start:
{
switch(lean_obj_tag(v_t_354_))
{
case 2:
{
lean_object* v_wi_356_; lean_object* v_alt_357_; lean_object* v___x_358_; 
v_wi_356_ = lean_ctor_get(v_t_354_, 0);
lean_inc_ref(v_wi_356_);
v_alt_357_ = lean_ctor_get(v_t_354_, 1);
lean_inc_ref(v_alt_357_);
lean_dec_ref(v_t_354_);
v___x_358_ = lean_apply_2(v_k_355_, v_wi_356_, v_alt_357_);
return v___x_358_;
}
case 3:
{
lean_object* v_indent_359_; lean_object* v_cls_360_; lean_object* v_msg_361_; uint8_t v_collapsed_362_; lean_object* v_children_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_indent_359_ = lean_ctor_get(v_t_354_, 0);
lean_inc(v_indent_359_);
v_cls_360_ = lean_ctor_get(v_t_354_, 1);
lean_inc(v_cls_360_);
v_msg_361_ = lean_ctor_get(v_t_354_, 2);
lean_inc_ref(v_msg_361_);
v_collapsed_362_ = lean_ctor_get_uint8(v_t_354_, sizeof(void*)*4);
v_children_363_ = lean_ctor_get(v_t_354_, 3);
lean_inc_ref(v_children_363_);
lean_dec_ref(v_t_354_);
v___x_364_ = lean_box(v_collapsed_362_);
v___x_365_ = lean_apply_5(v_k_355_, v_indent_359_, v_cls_360_, v_msg_361_, v___x_364_, v_children_363_);
return v___x_365_;
}
default: 
{
lean_object* v_a_366_; lean_object* v___x_367_; 
v_a_366_ = lean_ctor_get(v_t_354_, 0);
lean_inc_ref(v_a_366_);
lean_dec_ref(v_t_354_);
v___x_367_ = lean_apply_1(v_k_355_, v_a_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim(lean_object* v_motive__1_368_, lean_object* v_ctorIdx_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_k_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_370_, v_k_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_ctorElim___boxed(lean_object* v_motive__1_374_, lean_object* v_ctorIdx_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_k_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Widget_MsgEmbed_ctorElim(v_motive__1_374_, v_ctorIdx_375_, v_t_376_, v_h_377_, v_k_378_);
lean_dec(v_ctorIdx_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim___redArg(lean_object* v_t_380_, lean_object* v_expr_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_380_, v_expr_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_expr_elim(lean_object* v_motive__1_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_expr_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_384_, v_expr_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim___redArg(lean_object* v_t_388_, lean_object* v_goal_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_388_, v_goal_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_goal_elim(lean_object* v_motive__1_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_goal_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_392_, v_goal_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim___redArg(lean_object* v_t_396_, lean_object* v_widget_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_396_, v_widget_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_widget_elim(lean_object* v_motive__1_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_widget_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_400_, v_widget_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim___redArg(lean_object* v_t_404_, lean_object* v_trace_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_404_, v_trace_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_MsgEmbed_trace_elim(lean_object* v_motive__1_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_trace_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Widget_MsgEmbed_ctorElim___redArg(v_t_408_, v_trace_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0(void){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__0);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed_default(void){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_obj_once(&l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1, &l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1_once, _init_l_Lean_Widget_instInhabitedMsgEmbed_default___closed__1);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Widget_instInhabitedMsgEmbed(void){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Widget_instInhabitedMsgEmbed_default;
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx(lean_object* v_x_417_){
_start:
{
switch(lean_obj_tag(v_x_417_))
{
case 0:
{
lean_object* v___x_418_; 
v___x_418_ = lean_unsigned_to_nat(0u);
return v___x_418_;
}
case 1:
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(1u);
return v___x_419_;
}
case 2:
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(2u);
return v___x_420_;
}
default: 
{
lean_object* v___x_421_; 
v___x_421_ = lean_unsigned_to_nat(3u);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx___boxed(lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorIdx(v_x_422_);
lean_dec_ref(v_x_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(lean_object* v_t_424_, lean_object* v_k_425_){
_start:
{
switch(lean_obj_tag(v_t_424_))
{
case 2:
{
lean_object* v_wi_426_; lean_object* v_alt_427_; lean_object* v___x_428_; 
v_wi_426_ = lean_ctor_get(v_t_424_, 0);
lean_inc(v_wi_426_);
v_alt_427_ = lean_ctor_get(v_t_424_, 1);
lean_inc(v_alt_427_);
lean_dec_ref(v_t_424_);
v___x_428_ = lean_apply_2(v_k_425_, v_wi_426_, v_alt_427_);
return v___x_428_;
}
case 3:
{
lean_object* v_indent_429_; lean_object* v_cls_430_; lean_object* v_msg_431_; lean_object* v_collapsed_432_; lean_object* v_children_433_; lean_object* v___x_434_; 
v_indent_429_ = lean_ctor_get(v_t_424_, 0);
lean_inc(v_indent_429_);
v_cls_430_ = lean_ctor_get(v_t_424_, 1);
lean_inc(v_cls_430_);
v_msg_431_ = lean_ctor_get(v_t_424_, 2);
lean_inc(v_msg_431_);
v_collapsed_432_ = lean_ctor_get(v_t_424_, 3);
lean_inc(v_collapsed_432_);
v_children_433_ = lean_ctor_get(v_t_424_, 4);
lean_inc(v_children_433_);
lean_dec_ref(v_t_424_);
v___x_434_ = lean_apply_5(v_k_425_, v_indent_429_, v_cls_430_, v_msg_431_, v_collapsed_432_, v_children_433_);
return v___x_434_;
}
default: 
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_ctor_get(v_t_424_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v_t_424_);
v___x_436_ = lean_apply_1(v_k_425_, v_a_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(lean_object* v_motive_437_, lean_object* v_ctorIdx_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_k_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_439_, v_k_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___boxed(lean_object* v_motive_443_, lean_object* v_ctorIdx_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_k_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim(v_motive_443_, v_ctorIdx_444_, v_t_445_, v_h_446_, v_k_447_);
lean_dec(v_ctorIdx_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_449_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_449_, v_Lean_Widget_RpcEncodablePacket_expr_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_expr_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_Lean_Widget_RpcEncodablePacket_expr_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_453_, v_Lean_Widget_RpcEncodablePacket_expr_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_457_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_457_, v_Lean_Widget_RpcEncodablePacket_goal_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_goal_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_460_, lean_object* v_t_461_, lean_object* v_h_462_, lean_object* v_Lean_Widget_RpcEncodablePacket_goal_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_461_, v_Lean_Widget_RpcEncodablePacket_goal_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_465_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_465_, v_Lean_Widget_RpcEncodablePacket_widget_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_widget_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_Lean_Widget_RpcEncodablePacket_widget_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_469_, v_Lean_Widget_RpcEncodablePacket_widget_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim___redArg(lean_object* v_t_473_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_473_, v_Lean_Widget_RpcEncodablePacket_trace_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_RpcEncodablePacket_trace_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__elim(lean_object* v_motive_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_Lean_Widget_RpcEncodablePacket_trace_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Widget_RpcEncodablePacket_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__ctorElim___redArg(v_t_477_, v_Lean_Widget_RpcEncodablePacket_trace_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(lean_object* v_json_532_){
_start:
{
lean_object* v___x_533_; 
lean_inc(v_json_532_);
v___x_533_ = l_Lean_Json_getTag_x3f(v_json_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_534_; 
lean_dec(v_json_532_);
v___x_534_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_651_; 
v_val_535_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_651_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_651_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_val_535_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_651_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_box(0);
v___x_540_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_541_ = lean_string_dec_eq(v_val_535_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_543_ = lean_string_dec_eq(v_val_535_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
lean_del_object(v___x_537_);
v___x_544_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_545_ = lean_string_dec_eq(v_val_535_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_547_ = lean_string_dec_eq(v_val_535_, v___x_546_);
lean_dec(v_val_535_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_json_532_);
v___x_548_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(5u);
v___x_550_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_551_ = l_Lean_Json_parseCtorFields(v_json_532_, v___x_546_, v___x_549_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_578_; 
v_a_560_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_578_ == 0)
{
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_array_get(v___x_539_, v_a_560_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_array_get(v___x_539_, v_a_560_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(2u);
v___x_569_ = lean_array_get(v___x_539_, v_a_560_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(3u);
v___x_571_ = lean_array_get(v___x_539_, v_a_560_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(4u);
v___x_573_ = lean_array_get(v___x_539_, v_a_560_, v___x_572_);
lean_dec(v_a_560_);
v___x_574_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_574_, 0, v___x_565_);
lean_ctor_set(v___x_574_, 1, v___x_567_);
lean_ctor_set(v___x_574_, 2, v___x_569_);
lean_ctor_set(v___x_574_, 3, v___x_571_);
lean_ctor_set(v___x_574_, 4, v___x_573_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_574_);
v___x_576_ = v___x_562_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_val_535_);
v___x_579_ = lean_unsigned_to_nat(2u);
v___x_580_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_581_ = l_Lean_Json_parseCtorFields(v_json_532_, v___x_544_, v___x_579_, v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_602_; 
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_602_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_array_get(v___x_539_, v_a_590_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_array_get(v___x_539_, v_a_590_, v___x_596_);
lean_dec(v_a_590_);
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_598_);
v___x_600_ = v___x_592_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v_val_535_);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_box(0);
v___x_605_ = l_Lean_Json_parseCtorFields(v_json_532_, v___x_542_, v___x_603_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_537_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_626_; 
v_a_614_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_616_ = v___x_605_;
v_isShared_617_ = v_isSharedCheck_626_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_626_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_array_get(v___x_539_, v_a_614_, v___x_618_);
lean_dec(v_a_614_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
lean_ctor_set(v___x_537_, 0, v___x_619_);
v___x_621_ = v___x_537_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_621_);
v___x_623_ = v___x_616_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_val_535_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Json_parseCtorFields(v_json_532_, v___x_540_, v___x_627_, v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_del_object(v___x_537_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_650_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get(v___x_539_, v_a_638_, v___x_642_);
lean_dec(v_a_638_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_643_);
v___x_645_ = v___x_537_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_645_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(lean_object* v_x_654_){
_start:
{
switch(lean_obj_tag(v_x_654_))
{
case 0:
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_655_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v_x_654_);
v___x_656_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_655_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_Json_mkObj(v___x_659_);
return v___x_660_;
}
case 1:
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_661_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v_x_654_);
v___x_662_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_661_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_Json_mkObj(v___x_665_);
return v___x_666_;
}
case 2:
{
lean_object* v_wi_667_; lean_object* v_alt_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_686_; 
v_wi_667_ = lean_ctor_get(v_x_654_, 0);
v_alt_668_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_686_ == 0)
{
v___x_670_ = v_x_654_;
v_isShared_671_ = v_isSharedCheck_686_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_alt_668_);
lean_inc(v_wi_667_);
lean_dec(v_x_654_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_686_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_673_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 0);
lean_ctor_set(v___x_670_, 1, v_wi_667_);
lean_ctor_set(v___x_670_, 0, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_wi_667_);
v___x_675_ = v_reuseFailAlloc_685_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_676_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__20_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_alt_668_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_675_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_Json_mkObj(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_672_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_678_);
v___x_684_ = l_Lean_Json_mkObj(v___x_683_);
return v___x_684_;
}
}
}
default: 
{
lean_object* v_indent_687_; lean_object* v_cls_688_; lean_object* v_msg_689_; lean_object* v_collapsed_690_; lean_object* v_children_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_indent_687_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_indent_687_);
v_cls_688_ = lean_ctor_get(v_x_654_, 1);
lean_inc(v_cls_688_);
v_msg_689_ = lean_ctor_get(v_x_654_, 2);
lean_inc(v_msg_689_);
v_collapsed_690_ = lean_ctor_get(v_x_654_, 3);
lean_inc(v_collapsed_690_);
v_children_691_ = lean_ctor_get(v_x_654_, 4);
lean_inc(v_children_691_);
lean_dec_ref(v_x_654_);
v___x_692_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_693_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_indent_687_);
v___x_695_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_cls_688_);
v___x_697_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_msg_689_);
v___x_699_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_collapsed_690_);
v___x_701_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_));
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_children_691_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_700_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_698_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_696_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_694_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l_Lean_Json_mkObj(v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_692_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_703_);
v___x_712_ = l_Lean_Json_mkObj(v___x_711_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v___x_720_; lean_object* v_bs_x27_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v_v_719_ = lean_array_uget(v_bs_717_, v_i_716_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_bs_x27_721_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_720_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_716_, v___x_722_);
v___x_724_ = lean_array_uset(v_bs_x27_721_, v_i_716_, v_v_719_);
v_i_716_ = v___x_723_;
v_bs_717_ = v___x_724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9___boxed(lean_object* v_sz_726_, lean_object* v_i_727_, lean_object* v_bs_728_){
_start:
{
size_t v_sz_boxed_729_; size_t v_i_boxed_730_; lean_object* v_res_731_; 
v_sz_boxed_729_ = lean_unbox_usize(v_sz_726_);
lean_dec(v_sz_726_);
v_i_boxed_730_ = lean_unbox_usize(v_i_727_);
lean_dec(v_i_727_);
v_res_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_boxed_729_, v_i_boxed_730_, v_bs_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(lean_object* v_a_732_){
_start:
{
size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_sz_733_ = lean_array_size(v_a_732_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5_spec__9(v_sz_733_, v___x_734_, v_a_732_);
v___x_736_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(lean_object* v_x_740_){
_start:
{
switch(lean_obj_tag(v_x_740_))
{
case 0:
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_753_; 
v_a_741_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_743_ = v_x_740_;
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v_x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 3);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_741_);
v___x_747_ = v_reuseFailAlloc_752_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Json_mkObj(v___x_750_);
return v___x_751_;
}
}
}
case 1:
{
lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_a_754_ = lean_ctor_get(v_x_740_, 0);
lean_inc_ref(v_a_754_);
lean_dec_ref(v_x_740_);
v___x_755_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_756_ = l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(v_a_754_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Json_mkObj(v___x_759_);
return v___x_760_;
}
default: 
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_779_; 
v_a_761_ = lean_ctor_get(v_x_740_, 0);
v_a_762_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_779_ == 0)
{
v___x_764_ = v_x_740_;
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v_x_740_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_766_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_767_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_a_762_);
v___x_768_ = lean_unsigned_to_nat(2u);
v___x_769_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_770_ = lean_array_push(v___x_769_, v_a_761_);
v___x_771_ = lean_array_push(v___x_770_, v___x_767_);
v___x_772_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 0);
lean_ctor_set(v___x_764_, 1, v___x_772_);
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_774_ = v___x_764_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Json_mkObj(v___x_776_);
return v___x_777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(size_t v_sz_780_, size_t v_i_781_, lean_object* v_bs_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = lean_usize_dec_lt(v_i_781_, v_sz_780_);
if (v___x_783_ == 0)
{
return v_bs_782_;
}
else
{
lean_object* v_v_784_; lean_object* v___x_785_; lean_object* v_bs_x27_786_; lean_object* v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v_v_784_ = lean_array_uget(v_bs_782_, v_i_781_);
v___x_785_ = lean_unsigned_to_nat(0u);
v_bs_x27_786_ = lean_array_uset(v_bs_782_, v_i_781_, v___x_785_);
v___x_787_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_v_784_);
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_781_, v___x_788_);
v___x_790_ = lean_array_uset(v_bs_x27_786_, v_i_781_, v___x_787_);
v_i_781_ = v___x_789_;
v_bs_782_ = v___x_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2(lean_object* v_a_792_){
_start:
{
size_t v_sz_793_; size_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_sz_793_ = lean_array_size(v_a_792_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_793_, v___x_794_, v_a_792_);
v___x_796_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5___boxed(lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_bs_799_){
_start:
{
size_t v_sz_boxed_800_; size_t v_i_boxed_801_; lean_object* v_res_802_; 
v_sz_boxed_800_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_801_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1_spec__2_spec__5(v_sz_boxed_800_, v_i_boxed_801_, v_bs_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(lean_object* v_f_803_, lean_object* v_x_804_, lean_object* v___y_805_){
_start:
{
switch(lean_obj_tag(v_x_804_))
{
case 0:
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_f_803_);
v_a_806_ = lean_ctor_get(v_x_804_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v_x_804_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v_x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___y_805_);
return v___x_812_;
}
}
}
case 1:
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_834_; 
v_a_815_ = lean_ctor_get(v_x_804_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_834_ == 0)
{
v___x_817_ = v_x_804_;
v_isShared_818_ = v_isSharedCheck_834_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v_x_804_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_834_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
size_t v_sz_819_; size_t v___x_820_; lean_object* v___x_821_; lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_sz_819_ = lean_array_size(v_a_815_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_803_, v_sz_819_, v___x_820_, v_a_815_, v___y_805_);
v_fst_822_ = lean_ctor_get(v___x_821_, 0);
v_snd_823_ = lean_ctor_get(v___x_821_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_823_);
lean_inc(v_fst_822_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_fst_822_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_fst_822_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_snd_823_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
default: 
{
lean_object* v_a_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_856_; 
v_a_835_ = lean_ctor_get(v_x_804_, 0);
v_a_836_ = lean_ctor_get(v_x_804_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_856_ == 0)
{
v___x_838_ = v_x_804_;
v_isShared_839_ = v_isSharedCheck_856_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_inc(v_a_835_);
lean_dec(v_x_804_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_856_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_855_; 
lean_inc_ref(v_f_803_);
v___x_840_ = lean_apply_2(v_f_803_, v_a_835_, v___y_805_);
v_fst_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_841_);
v_snd_842_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_842_);
lean_dec_ref(v___x_840_);
v___x_843_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_803_, v_a_836_, v_snd_842_);
v_fst_844_ = lean_ctor_get(v___x_843_, 0);
v_snd_845_ = lean_ctor_get(v___x_843_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_855_ == 0)
{
v___x_847_ = v___x_843_;
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_inc(v_fst_844_);
lean_dec(v___x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_fst_844_);
lean_ctor_set(v___x_838_, 0, v_fst_841_);
v___x_850_ = v___x_838_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_fst_841_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_fst_844_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_850_);
v___x_852_ = v___x_847_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_snd_845_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(lean_object* v_f_857_, size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_, lean_object* v___y_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_f_857_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_bs_860_);
lean_ctor_set(v___x_863_, 1, v___y_861_);
return v___x_863_;
}
else
{
lean_object* v_v_864_; lean_object* v___x_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___x_868_; lean_object* v_bs_x27_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v_v_864_ = lean_array_uget_borrowed(v_bs_860_, v_i_859_);
lean_inc(v_v_864_);
lean_inc_ref(v_f_857_);
v___x_865_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v_f_857_, v_v_864_, v___y_861_);
v_fst_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_fst_866_);
v_snd_867_ = lean_ctor_get(v___x_865_, 1);
lean_inc(v_snd_867_);
lean_dec_ref(v___x_865_);
v___x_868_ = lean_unsigned_to_nat(0u);
v_bs_x27_869_ = lean_array_uset(v_bs_860_, v_i_859_, v___x_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_859_, v___x_870_);
v___x_872_ = lean_array_uset(v_bs_x27_869_, v_i_859_, v_fst_866_);
v_i_859_ = v___x_871_;
v_bs_860_ = v___x_872_;
v___y_861_ = v_snd_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg___boxed(lean_object* v_f_874_, lean_object* v_sz_875_, lean_object* v_i_876_, lean_object* v_bs_877_, lean_object* v___y_878_){
_start:
{
size_t v_sz_boxed_879_; size_t v_i_boxed_880_; lean_object* v_res_881_; 
v_sz_boxed_879_ = lean_unbox_usize(v_sz_875_);
lean_dec(v_sz_875_);
v_i_boxed_880_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_874_, v_sz_boxed_879_, v_i_boxed_880_, v_bs_877_, v___y_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(lean_object* v_x_883_, lean_object* v_a_884_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_906_; 
v_a_885_ = lean_ctor_get(v_x_883_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_906_ == 0)
{
v___x_887_ = v_x_883_;
v_isShared_888_ = v_isSharedCheck_906_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v_x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_906_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_905_; 
v_sz_889_ = lean_array_size(v_a_885_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_889_, v___x_890_, v_a_885_, v_a_884_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
v_snd_893_ = lean_ctor_get(v___x_891_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_905_ == 0)
{
v___x_895_ = v___x_891_;
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_snd_893_);
lean_inc(v_fst_892_);
lean_dec(v___x_891_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__5(v_fst_892_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_897_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_904_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_899_);
lean_dec_ref(v___x_899_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_900_);
v___x_902_ = v___x_895_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_893_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_926_; 
v_a_907_ = lean_ctor_get(v_x_883_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_926_ == 0)
{
v___x_909_ = v_x_883_;
v_isShared_910_ = v_isSharedCheck_926_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v_x_883_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_926_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_fst_913_; lean_object* v_snd_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_925_; 
v___x_911_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_912_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v___x_911_, v_a_907_, v_a_884_);
lean_dec(v_a_907_);
v_fst_913_ = lean_ctor_get(v___x_912_, 0);
v_snd_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_925_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snd_914_);
lean_inc(v_fst_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_925_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_fst_913_);
v___x_919_ = v___x_909_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_fst_913_);
v___x_919_ = v_reuseFailAlloc_924_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_37_(v___x_919_);
lean_dec_ref(v___x_919_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_snd_914_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_x_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
switch(lean_obj_tag(v_x_927_))
{
case 0:
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v___x_929_);
v_a_930_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_950_ == 0)
{
v___x_932_ = v_x_927_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v_x_927_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_949_; 
v___x_934_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_935_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_934_, v_a_930_, v_a_928_);
v_fst_936_ = lean_ctor_get(v___x_935_, 0);
v_snd_937_ = lean_ctor_get(v___x_935_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_949_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_936_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_943_ = v___x_932_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_948_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_943_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_944_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_937_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
case 1:
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___x_929_);
v_a_951_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_969_ == 0)
{
v___x_953_ = v_x_927_;
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v_x_927_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v___x_955_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_951_, v_a_928_);
v_fst_956_ = lean_ctor_get(v___x_955_, 0);
v_snd_957_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_968_ == 0)
{
v___x_959_ = v___x_955_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_snd_957_);
lean_inc(v_fst_956_);
lean_dec(v___x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_fst_956_);
v___x_962_ = v___x_953_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_fst_956_);
v___x_962_ = v_reuseFailAlloc_967_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_962_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_963_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_snd_957_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
case 2:
{
lean_object* v_wi_970_; lean_object* v_alt_971_; lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_993_; 
v_wi_970_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_wi_970_);
v_alt_971_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_alt_971_);
lean_dec_ref(v_x_927_);
v___x_972_ = l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_970_, v_a_928_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
v_snd_974_ = lean_ctor_get(v___x_972_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_993_ == 0)
{
v___x_976_ = v___x_972_;
v_isShared_977_ = v_isSharedCheck_993_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_974_);
lean_inc(v_fst_973_);
lean_dec(v___x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_993_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_992_; 
v___x_978_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_929_, v_alt_971_, v_snd_974_);
v_fst_979_ = lean_ctor_get(v___x_978_, 0);
v_snd_980_ = lean_ctor_get(v___x_978_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_992_ == 0)
{
v___x_982_ = v___x_978_;
v_isShared_983_ = v_isSharedCheck_992_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snd_980_);
lean_inc(v_fst_979_);
lean_dec(v___x_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_992_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_979_);
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 2);
lean_ctor_set(v___x_976_, 1, v___x_984_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_973_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_986_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_987_);
v___x_989_ = v___x_982_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_980_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
default: 
{
lean_object* v_indent_994_; lean_object* v_cls_995_; lean_object* v_msg_996_; uint8_t v_collapsed_997_; lean_object* v_children_998_; lean_object* v___x_999_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1002_; lean_object* v_fst_1003_; lean_object* v_snd_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1020_; 
v_indent_994_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_indent_994_);
v_cls_995_ = lean_ctor_get(v_x_927_, 1);
lean_inc(v_cls_995_);
v_msg_996_ = lean_ctor_get(v_x_927_, 2);
lean_inc_ref(v_msg_996_);
v_collapsed_997_ = lean_ctor_get_uint8(v_x_927_, sizeof(void*)*4);
v_children_998_ = lean_ctor_get(v_x_927_, 3);
lean_inc_ref(v_children_998_);
lean_dec_ref(v_x_927_);
v___x_999_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_929_, v_msg_996_, v_a_928_);
v_fst_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_fst_1000_);
v_snd_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_999_);
v___x_1002_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2(v_children_998_, v_snd_1001_);
v_fst_1003_ = lean_ctor_get(v___x_1002_, 0);
v_snd_1004_ = lean_ctor_get(v___x_1002_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1006_ = v___x_1002_;
v_isShared_1007_ = v_isSharedCheck_1020_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snd_1004_);
lean_inc(v_fst_1003_);
lean_dec(v___x_1002_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1020_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1008_ = l_Lean_JsonNumber_fromNat(v_indent_994_);
v___x_1009_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = 1;
v___x_1011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_cls_995_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_1000_);
v___x_1014_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1014_, 0, v_collapsed_997_);
v___x_1015_ = lean_alloc_ctor(3, 5, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1009_);
lean_ctor_set(v___x_1015_, 1, v___x_1012_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
lean_ctor_set(v___x_1015_, 4, v_fst_1003_);
v___x_1016_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_64_(v___x_1015_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1016_);
v___x_1018_ = v___x_1006_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_snd_1004_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(size_t v_sz_1021_, size_t v_i_1022_, lean_object* v_bs_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_lt(v_i_1022_, v_sz_1021_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_bs_1023_);
lean_ctor_set(v___x_1026_, 1, v___y_1024_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; lean_object* v_v_1028_; lean_object* v___x_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1032_; lean_object* v_bs_x27_1033_; lean_object* v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1027_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_), 2, 0);
v_v_1028_ = lean_array_uget_borrowed(v_bs_1023_, v_i_1022_);
lean_inc(v_v_1028_);
v___x_1029_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0___redArg(v___x_1027_, v_v_1028_, v___y_1024_);
v_fst_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_fst_1030_);
v_snd_1031_ = lean_ctor_get(v___x_1029_, 1);
lean_inc(v_snd_1031_);
lean_dec_ref(v___x_1029_);
v___x_1032_ = lean_unsigned_to_nat(0u);
v_bs_x27_1033_ = lean_array_uset(v_bs_1023_, v_i_1022_, v___x_1032_);
v___x_1034_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1(v_fst_1030_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_add(v_i_1022_, v___x_1035_);
v___x_1037_ = lean_array_uset(v_bs_x27_1033_, v_i_1022_, v___x_1034_);
v_i_1022_ = v___x_1036_;
v_bs_1023_ = v___x_1037_;
v___y_1024_ = v_snd_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4___boxed(lean_object* v_sz_1039_, lean_object* v_i_1040_, lean_object* v_bs_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_sz_boxed_1043_; size_t v_i_boxed_1044_; lean_object* v_res_1045_; 
v_sz_boxed_1043_ = lean_unbox_usize(v_sz_1039_);
lean_dec(v_sz_1039_);
v_i_boxed_1044_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__2_spec__4(v_sz_boxed_1043_, v_i_boxed_1044_, v_bs_1041_, v___y_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(lean_object* v_x_1046_){
_start:
{
lean_inc_ref(v_x_1046_);
return v_x_1046_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg___boxed(lean_object* v_x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___redArg(v_x_1047_);
lean_dec_ref(v_x_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(lean_object* v_00_u03b1_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_){
_start:
{
lean_inc_ref(v_x_1050_);
return v_x_1050_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__6(v_00_u03b1_1052_, v_x_1053_, v___y_1054_);
lean_dec_ref(v___y_1054_);
lean_dec_ref(v_x_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(lean_object* v_json_1062_){
_start:
{
lean_object* v___x_1063_; 
lean_inc(v_json_1062_);
v___x_1063_ = l_Lean_Json_getTag_x3f(v_json_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; 
lean_dec(v_json_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__0));
return v___x_1064_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1171_; 
v_val_1065_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1171_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1171_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__1));
v___x_1071_ = lean_string_dec_eq(v_val_1065_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__0));
v___x_1073_ = lean_string_dec_eq(v_val_1065_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
lean_del_object(v___x_1067_);
v___x_1074_ = ((lean_object*)(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__1___closed__2));
v___x_1075_ = lean_string_dec_eq(v_val_1065_, v___x_1074_);
lean_dec(v_val_1065_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_json_1062_);
v___x_1076_ = ((lean_object*)(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4___closed__1));
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_unsigned_to_nat(2u);
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Lean_Json_parseCtorFields(v_json_1062_, v___x_1074_, v___x_1077_, v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1088_);
lean_dec_ref(v___x_1079_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_array_get_borrowed(v___x_1069_, v_a_1088_, v___x_1089_);
lean_inc(v___x_1090_);
v___x_1091_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_dec(v_a_1088_);
return v___x_1091_;
}
else
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
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_array_get(v___x_1069_, v_a_1088_, v___x_1096_);
lean_dec(v_a_1088_);
v___x_1098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1098_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_val_1065_);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_Json_parseCtorFields(v_json_1062_, v___x_1072_, v___x_1103_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_del_object(v___x_1067_);
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
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1105_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_array_get(v___x_1069_, v_a_1114_, v___x_1115_);
lean_dec(v_a_1114_);
v___x_1117_ = l_Lean_Json_getStr_x3f(v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_del_object(v___x_1067_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1136_; 
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 0);
lean_ctor_set(v___x_1067_, 0, v_a_1126_);
v___x_1131_ = v___x_1067_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_val_1065_);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_box(0);
v___x_1139_ = l_Lean_Json_parseCtorFields(v_json_1062_, v___x_1070_, v___x_1137_, v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1067_);
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
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1139_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_array_get(v___x_1069_, v_a_1148_, v___x_1149_);
lean_dec(v_a_1148_);
v___x_1151_ = l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1067_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1170_; 
v_a_1160_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1162_ = v___x_1151_;
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1151_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v_a_1160_);
v___x_1165_ = v___x_1067_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(size_t v_sz_1172_, size_t v_i_1173_, lean_object* v_bs_1174_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_usize_dec_lt(v_i_1173_, v_sz_1172_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_bs_1174_);
return v___x_1176_;
}
else
{
lean_object* v_v_1177_; lean_object* v___x_1178_; 
v_v_1177_ = lean_array_uget_borrowed(v_bs_1174_, v_i_1173_);
lean_inc(v_v_1177_);
v___x_1178_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_bs_1174_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v_bs_x27_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v_a_1187_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1178_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v_bs_x27_1189_ = lean_array_uset(v_bs_1174_, v_i_1173_, v___x_1188_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1173_, v___x_1190_);
v___x_1192_ = lean_array_uset(v_bs_x27_1189_, v_i_1173_, v_a_1187_);
v_i_1173_ = v___x_1191_;
v_bs_1174_ = v___x_1192_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8(lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 4)
{
lean_object* v_elems_1195_; size_t v_sz_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_elems_1195_ = lean_ctor_get(v_x_1194_, 0);
lean_inc_ref(v_elems_1195_);
lean_dec_ref(v_x_1194_);
v_sz_1196_ = lean_array_size(v_elems_1195_);
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_1196_, v___x_1197_, v_elems_1195_);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1199_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1200_ = lean_unsigned_to_nat(80u);
v___x_1201_ = l_Lean_Json_pretty(v_x_1194_, v___x_1200_);
v___x_1202_ = lean_string_append(v___x_1199_, v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12___boxed(lean_object* v_sz_1206_, lean_object* v_i_1207_, lean_object* v_bs_1208_){
_start:
{
size_t v_sz_boxed_1209_; size_t v_i_boxed_1210_; lean_object* v_res_1211_; 
v_sz_boxed_1209_ = lean_unbox_usize(v_sz_1206_);
lean_dec(v_sz_1206_);
v_i_boxed_1210_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8_spec__12(v_sz_boxed_1209_, v_i_boxed_1210_, v_bs_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(lean_object* v_f_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_){
_start:
{
switch(lean_obj_tag(v_x_1213_))
{
case 0:
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_f_1212_);
v_a_1215_ = lean_ctor_get(v_x_1213_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_x_1213_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v_x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
case 1:
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1250_; 
v_a_1224_ = lean_ctor_get(v_x_1213_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1226_ = v_x_1213_;
v_isShared_1227_ = v_isSharedCheck_1250_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v_x_1213_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1250_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_sz_1228_ = lean_array_size(v_a_1224_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1212_, v_sz_1228_, v___x_1229_, v_a_1224_, v___y_1214_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_del_object(v___x_1226_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1249_; 
v_a_1239_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1241_ = v___x_1230_;
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1230_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_a_1239_);
v___x_1244_ = v___x_1226_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
default: 
{
lean_object* v_a_1251_; lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1278_; 
v_a_1251_ = lean_ctor_get(v_x_1213_, 0);
v_a_1252_ = lean_ctor_get(v_x_1213_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1254_ = v_x_1213_;
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_inc(v_a_1251_);
lean_dec(v_x_1213_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; 
lean_inc_ref(v_f_1212_);
lean_inc_ref(v___y_1214_);
v___x_1256_ = lean_apply_2(v_f_1212_, v_a_1251_, v___y_1214_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_del_object(v___x_1254_);
lean_dec_ref(v_a_1252_);
lean_dec_ref(v_f_1212_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1256_);
v___x_1266_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1212_, v_a_1252_, v___y_1214_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_dec(v_a_1265_);
lean_del_object(v___x_1254_);
return v___x_1266_;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1277_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v_a_1267_);
lean_ctor_set(v___x_1254_, 0, v_a_1265_);
v___x_1272_ = v___x_1254_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_a_1267_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(lean_object* v_f_1279_, size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_bs_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref(v_f_1279_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_bs_1282_);
return v___x_1285_;
}
else
{
lean_object* v_v_1286_; lean_object* v___x_1287_; 
v_v_1286_ = lean_array_uget_borrowed(v_bs_1282_, v_i_1281_);
lean_inc(v_v_1286_);
lean_inc_ref(v_f_1279_);
v___x_1287_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1279_, v_v_1286_, v___y_1283_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_bs_1282_);
lean_dec_ref(v_f_1279_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v_bs_x27_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_a_1296_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v___x_1287_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v_bs_x27_1298_ = lean_array_uset(v_bs_1282_, v_i_1281_, v___x_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1281_, v___x_1299_);
v___x_1301_ = lean_array_uset(v_bs_x27_1298_, v_i_1281_, v_a_1296_);
v_i_1281_ = v___x_1300_;
v_bs_1282_ = v___x_1301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg___boxed(lean_object* v_f_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_bs_1306_, lean_object* v___y_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1303_, v_sz_boxed_1308_, v_i_boxed_1309_, v_bs_1306_, v___y_1307_);
lean_dec_ref(v___y_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg___boxed(lean_object* v_f_1311_, lean_object* v_x_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v_f_1311_, v_x_1312_, v___y_1313_);
lean_dec_ref(v___y_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_bs_1317_);
return v___x_1319_;
}
else
{
lean_object* v_v_1320_; lean_object* v___x_1321_; lean_object* v_bs_x27_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v_v_1320_ = lean_array_uget(v_bs_1317_, v_i_1316_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v_bs_x27_1322_ = lean_array_uset(v_bs_1317_, v_i_1316_, v___x_1321_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1316_, v___x_1323_);
v___x_1325_ = lean_array_uset(v_bs_x27_1322_, v_i_1316_, v_v_1320_);
v_i_1316_ = v___x_1324_;
v_bs_1317_ = v___x_1325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17___boxed(lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_bs_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_boxed_1330_, v_i_boxed_1331_, v_bs_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(lean_object* v_x_1333_){
_start:
{
if (lean_obj_tag(v_x_1333_) == 4)
{
lean_object* v_elems_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v_elems_1334_ = lean_ctor_get(v_x_1333_, 0);
lean_inc_ref(v_elems_1334_);
lean_dec_ref(v_x_1333_);
v_sz_1335_ = lean_array_size(v_elems_1334_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13_spec__17(v_sz_1335_, v___x_1336_, v_elems_1334_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1338_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__0));
v___x_1339_ = lean_unsigned_to_nat(80u);
v___x_1340_ = l_Lean_Json_pretty(v_x_1333_, v___x_1339_);
v___x_1341_ = lean_string_append(v___x_1338_, v___x_1340_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_1343_ = lean_string_append(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(lean_object* v_j_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_29703178____hygCtx___hyg_17_(v_j_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1348_);
if (lean_obj_tag(v_a_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1394_; 
v_a_1358_ = lean_ctor_get(v_a_1357_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_a_1357_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1360_ = v_a_1357_;
v_isShared_1361_ = v_isSharedCheck_1394_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v_a_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1394_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__13(v_a_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1360_);
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; size_t v_sz_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v_a_1371_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1362_);
v_sz_1372_ = lean_array_size(v_a_1371_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(v_sz_1372_, v___x_1373_, v_a_1371_, v_a_1347_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1360_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v___x_1374_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_a_1383_);
v___x_1388_ = v___x_1360_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1388_);
v___x_1390_ = v___x_1385_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1420_; 
v_a_1395_ = lean_ctor_get(v_a_1357_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_a_1357_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1397_ = v_a_1357_;
v_isShared_1398_ = v_isSharedCheck_1420_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v_a_1357_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1420_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_Widget_instImpl_00___x40_Lean_Widget_InteractiveDiagnostic_72002168____hygCtx___hyg_14_));
v___x_1400_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_1399_, v_a_1395_, v_a_1347_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_del_object(v___x_1397_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1419_; 
v_a_1409_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1411_ = v___x_1400_;
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1400_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_a_1409_);
v___x_1414_ = v___x_1397_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(lean_object* v_j_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_2315129857____hygCtx___hyg_37_(v_j_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1423_);
v___x_1433_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
switch(lean_obj_tag(v_a_1432_))
{
case 0:
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v___x_1433_);
v_a_1434_ = lean_ctor_get(v_a_1432_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_a_1432_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1436_ = v_a_1432_;
v_isShared_1437_ = v_isSharedCheck_1469_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v_a_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1469_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_a_1434_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1436_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1438_);
v___x_1448_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_));
v___x_1449_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1448_, v_a_1447_, v_a_1422_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_del_object(v___x_1436_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_a_1458_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v___x_1449_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1449_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_a_1458_);
v___x_1463_ = v___x_1436_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v___x_1433_);
v_a_1470_ = lean_ctor_get(v_a_1432_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_a_1432_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1472_ = v_a_1432_;
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v_a_1432_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_a_1470_, v_a_1422_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_del_object(v___x_1472_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1493_; 
v_a_1483_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1485_ = v___x_1474_;
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1474_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v_a_1483_);
v___x_1488_ = v___x_1472_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1488_);
v___x_1490_ = v___x_1485_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
case 2:
{
lean_object* v_wi_1495_; lean_object* v_alt_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1540_; 
v_wi_1495_ = lean_ctor_get(v_a_1432_, 0);
v_alt_1496_ = lean_ctor_get(v_a_1432_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_a_1432_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1498_ = v_a_1432_;
v_isShared_1499_ = v_isSharedCheck_1540_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_alt_1496_);
lean_inc(v_wi_1495_);
lean_dec(v_a_1432_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1540_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_wi_1495_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1498_);
lean_dec(v_alt_1496_);
lean_dec_ref(v___x_1433_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1500_);
v___x_1510_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_alt_1496_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_a_1509_);
lean_del_object(v___x_1498_);
lean_dec_ref(v___x_1433_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1510_);
v___x_1520_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1433_, v_a_1519_, v_a_1422_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_a_1509_);
lean_del_object(v___x_1498_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1539_; 
v_a_1529_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1531_ = v___x_1520_;
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1520_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_a_1529_);
lean_ctor_set(v___x_1498_, 0, v_a_1509_);
v___x_1534_ = v___x_1498_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1509_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
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
lean_object* v_indent_1541_; lean_object* v_cls_1542_; lean_object* v_msg_1543_; lean_object* v_collapsed_1544_; lean_object* v_children_1545_; lean_object* v___x_1546_; 
v_indent_1541_ = lean_ctor_get(v_a_1432_, 0);
lean_inc(v_indent_1541_);
v_cls_1542_ = lean_ctor_get(v_a_1432_, 1);
lean_inc(v_cls_1542_);
v_msg_1543_ = lean_ctor_get(v_a_1432_, 2);
lean_inc(v_msg_1543_);
v_collapsed_1544_ = lean_ctor_get(v_a_1432_, 3);
lean_inc(v_collapsed_1544_);
v_children_1545_ = lean_ctor_get(v_a_1432_, 4);
lean_inc(v_children_1545_);
lean_dec_ref(v_a_1432_);
v___x_1546_ = l_Lean_Json_getNat_x3f(v_indent_1541_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_children_1545_);
lean_dec(v_collapsed_1544_);
lean_dec(v_msg_1543_);
lean_dec(v_cls_1542_);
lean_dec_ref(v___x_1433_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1546_);
v___x_1556_ = l_Lean_Name_fromJson_x3f(v_cls_1542_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1555_);
lean_dec(v_children_1545_);
lean_dec(v_collapsed_1544_);
lean_dec(v_msg_1543_);
lean_dec_ref(v___x_1433_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1556_);
v___x_1566_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_msg_1543_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1555_);
lean_dec(v_children_1545_);
lean_dec(v_collapsed_1544_);
lean_dec_ref(v___x_1433_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1566_);
v___x_1576_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1433_, v_a_1575_, v_a_1422_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1555_);
lean_dec(v_children_1545_);
lean_dec(v_collapsed_1544_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1576_);
v___x_1586_ = l_Lean_Json_getBool_x3f(v_collapsed_1544_);
lean_dec(v_collapsed_1544_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1565_);
lean_dec(v_a_1555_);
lean_dec(v_children_1545_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1586_);
v___x_1596_ = l_Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7(v_children_1545_, v_a_1422_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1585_);
lean_dec(v_a_1565_);
lean_dec(v_a_1555_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v_a_1605_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1607_ = v___x_1596_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1596_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_1609_, 0, v_a_1555_);
lean_ctor_set(v___x_1609_, 1, v_a_1565_);
lean_ctor_set(v___x_1609_, 2, v_a_1585_);
lean_ctor_set(v___x_1609_, 3, v_a_1605_);
v___x_1610_ = lean_unbox(v_a_1595_);
lean_dec(v_a_1595_);
lean_ctor_set_uint8(v___x_1609_, sizeof(void*)*4, v___x_1610_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1609_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed(lean_object* v_j_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1_(v_j_1615_, v_a_1616_);
lean_dec_ref(v_a_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableStrictOrLazy_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2157017296____hygCtx___hyg_1____at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__7_spec__14(size_t v_sz_1618_, size_t v_i_1619_, lean_object* v_bs_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_usize_dec_lt(v_i_1619_, v_sz_1618_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_bs_1620_);
return v___x_1623_;
}
else
{
lean_object* v_v_1624_; lean_object* v___x_1625_; 
v_v_1624_ = lean_array_uget_borrowed(v_bs_1620_, v_i_1619_);
lean_inc(v_v_1624_);
v___x_1625_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4(v_v_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_bs_1620_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1625_);
v___x_1635_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1____boxed), 2, 0);
v___x_1636_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5___redArg(v___x_1635_, v_a_1634_, v___y_1621_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_bs_1620_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1646_; lean_object* v_bs_x27_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v_a_1645_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1636_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v_bs_x27_1647_ = lean_array_uset(v_bs_1620_, v_i_1619_, v___x_1646_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_add(v_i_1619_, v___x_1648_);
v___x_1650_ = lean_array_uset(v_bs_x27_1647_, v_i_1619_, v_a_1645_);
v_i_1619_ = v___x_1649_;
v_bs_1620_ = v___x_1650_;
goto _start;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_f_1682_, size_t v_sz_1683_, size_t v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___redArg(v_f_1682_, v_sz_1683_, v_i_1684_, v_bs_1685_, v___y_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_f_1690_, lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_bs_1693_, lean_object* v___y_1694_){
_start:
{
size_t v_sz_boxed_1695_; size_t v_i_boxed_1696_; lean_object* v_res_1697_; 
v_sz_boxed_1695_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1696_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v_res_1697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_enc_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__0_spec__0(v_00_u03b1_1688_, v_00_u03b2_1689_, v_f_1690_, v_sz_boxed_1695_, v_i_boxed_1696_, v_bs_1693_, v___y_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(lean_object* v_00_u03b1_1698_, lean_object* v_00_u03b2_1699_, lean_object* v_f_1700_, size_t v_sz_1701_, size_t v_i_1702_, lean_object* v_bs_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___redArg(v_f_1700_, v_sz_1701_, v_i_1702_, v_bs_1703_, v___y_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_f_1708_, lean_object* v_sz_1709_, lean_object* v_i_1710_, lean_object* v_bs_1711_, lean_object* v___y_1712_){
_start:
{
size_t v_sz_boxed_1713_; size_t v_i_boxed_1714_; lean_object* v_res_1715_; 
v_sz_boxed_1713_ = lean_unbox_usize(v_sz_1709_);
lean_dec(v_sz_1709_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__5_spec__10(v_00_u03b1_1706_, v_00_u03b2_1707_, v_f_1708_, v_sz_boxed_1713_, v_i_boxed_1714_, v_bs_1711_, v___y_1712_);
lean_dec_ref(v___y_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(lean_object* v_j_1729_, lean_object* v_k_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = l_Lean_Json_getObjValD(v_j_1729_, v_k_1730_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0___boxed(lean_object* v_j_1733_, lean_object* v_k_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_j_1733_, v_k_1734_);
lean_dec_ref(v_k_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(lean_object* v_x_1738_){
_start:
{
if (lean_obj_tag(v_x_1738_) == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1___closed__0));
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_x_1738_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(lean_object* v_j_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_Lean_Json_getObjValD(v_j_1742_, v_k_1743_);
v___x_1745_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1_spec__1(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1___boxed(lean_object* v_j_1746_, lean_object* v_k_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_j_1746_, v_k_1747_);
lean_dec_ref(v_k_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(lean_object* v_json_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_a_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1801_; 
v___x_1761_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc_n(v_json_1760_, 10);
v___x_1762_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1760_, v___x_1761_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1765_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1764_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1768_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1767_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1771_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1770_);
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1774_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1773_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1777_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1776_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1780_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__0(v_json_1760_, v___x_1779_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1783_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1782_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1786_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1785_);
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1789_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1788_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1792_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39__spec__1(v_json_1760_, v___x_1791_);
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1801_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1763_);
lean_ctor_set(v___x_1797_, 1, v_a_1766_);
lean_ctor_set(v___x_1797_, 2, v_a_1769_);
lean_ctor_set(v___x_1797_, 3, v_a_1772_);
lean_ctor_set(v___x_1797_, 4, v_a_1775_);
lean_ctor_set(v___x_1797_, 5, v_a_1778_);
lean_ctor_set(v___x_1797_, 6, v_a_1781_);
lean_ctor_set(v___x_1797_, 7, v_a_1784_);
lean_ctor_set(v___x_1797_, 8, v_a_1787_);
lean_ctor_set(v___x_1797_, 9, v_a_1790_);
lean_ctor_set(v___x_1797_, 10, v_a_1793_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1797_);
v___x_1799_ = v___x_1795_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(lean_object* v_k_1804_, lean_object* v_x_1805_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref(v_k_1804_);
v___x_1806_ = lean_box(0);
return v___x_1806_;
}
else
{
lean_object* v_val_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_val_1807_ = lean_ctor_get(v_x_1805_, 0);
lean_inc(v_val_1807_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_k_1804_);
lean_ctor_set(v___x_1808_, 1, v_val_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0___boxed(lean_object* v_k_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v_k_1811_, v_x_1812_);
lean_dec(v_x_1812_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__1(lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
if (lean_obj_tag(v_a_1814_) == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_array_to_list(v_a_1815_);
return v___x_1816_;
}
else
{
lean_object* v_head_1817_; lean_object* v_tail_1818_; lean_object* v___x_1819_; 
v_head_1817_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_head_1817_);
v_tail_1818_ = lean_ctor_get(v_a_1814_, 1);
lean_inc(v_tail_1818_);
lean_dec_ref(v_a_1814_);
v___x_1819_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1815_, v_head_1817_);
v_a_1814_ = v_tail_1818_;
v_a_1815_ = v___x_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(lean_object* v_x_1823_){
_start:
{
lean_object* v_range_1824_; lean_object* v_fullRange_x3f_1825_; lean_object* v_severity_x3f_1826_; lean_object* v_isSilent_x3f_1827_; lean_object* v_code_x3f_1828_; lean_object* v_source_x3f_1829_; lean_object* v_message_1830_; lean_object* v_tags_x3f_1831_; lean_object* v_leanTags_x3f_1832_; lean_object* v_relatedInformation_x3f_1833_; lean_object* v_data_x3f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_range_1824_ = lean_ctor_get(v_x_1823_, 0);
v_fullRange_x3f_1825_ = lean_ctor_get(v_x_1823_, 1);
v_severity_x3f_1826_ = lean_ctor_get(v_x_1823_, 2);
v_isSilent_x3f_1827_ = lean_ctor_get(v_x_1823_, 3);
v_code_x3f_1828_ = lean_ctor_get(v_x_1823_, 4);
v_source_x3f_1829_ = lean_ctor_get(v_x_1823_, 5);
v_message_1830_ = lean_ctor_get(v_x_1823_, 6);
v_tags_x3f_1831_ = lean_ctor_get(v_x_1823_, 7);
v_leanTags_x3f_1832_ = lean_ctor_get(v_x_1823_, 8);
v_relatedInformation_x3f_1833_ = lean_ctor_get(v_x_1823_, 9);
v_data_x3f_1834_ = lean_ctor_get(v_x_1823_, 10);
v___x_1835_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_range_1824_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_range_1824_);
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1840_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1839_, v_fullRange_x3f_1825_);
v___x_1841_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1842_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1841_, v_severity_x3f_1826_);
v___x_1843_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1844_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1843_, v_isSilent_x3f_1827_);
v___x_1845_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1846_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1845_, v_code_x3f_1828_);
v___x_1847_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1848_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1847_, v_source_x3f_1829_);
v___x_1849_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
lean_inc(v_message_1830_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_message_1830_);
v___x_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1837_);
v___x_1852_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1853_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1852_, v_tags_x3f_1831_);
v___x_1854_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1855_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1854_, v_leanTags_x3f_1832_);
v___x_1856_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1857_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1856_, v_relatedInformation_x3f_1833_);
v___x_1858_ = ((lean_object*)(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_));
v___x_1859_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__0(v___x_1858_, v_data_x3f_1834_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1837_);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1857_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1855_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1853_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1851_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1848_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1846_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1844_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1842_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1840_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1838_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = ((lean_object*)(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_));
v___x_1872_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57__spec__1(v___x_1870_, v___x_1871_);
v___x_1873_ = l_Lean_Json_mkObj(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57____boxed(lean_object* v_x_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(v_x_1874_);
lean_dec_ref(v_x_1874_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = l_Lean_JsonNumber_fromNat(v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1881_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_unsigned_to_nat(2u);
v___x_1883_ = l_Lean_JsonNumber_fromNat(v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1885_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1886_, lean_object* v___y_1887_){
_start:
{
if (v_a_1886_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___y_1887_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___y_1887_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_a_boxed_1894_; lean_object* v_res_1895_; 
v_a_boxed_1894_ = lean_unbox(v_a_1892_);
v_res_1895_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1894_, v___y_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_a_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_a_1896_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___y_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(uint8_t v_a_1900_, lean_object* v___y_1901_){
_start:
{
if (v_a_1900_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___y_1901_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___y_1901_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_a_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v_a_boxed_1908_; lean_object* v_res_1909_; 
v_a_boxed_1908_ = lean_unbox(v_a_1906_);
v_res_1909_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_a_boxed_1908_, v___y_1907_);
return v_res_1909_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_unsigned_to_nat(3u);
v___x_1960_ = l_Lean_JsonNumber_fromNat(v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__24_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1962_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_unsigned_to_nat(4u);
v___x_1964_ = l_Lean_JsonNumber_fromNat(v___x_1963_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__26_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_1966_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_range_1970_; lean_object* v_fullRange_x3f_1971_; lean_object* v_severity_x3f_1972_; lean_object* v_isSilent_x3f_1973_; lean_object* v_code_x3f_1974_; lean_object* v_source_x3f_1975_; lean_object* v_message_1976_; lean_object* v_tags_x3f_1977_; lean_object* v_leanTags_x3f_1978_; lean_object* v_relatedInformation_x3f_1979_; lean_object* v_data_x3f_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2175_; 
v_range_1970_ = lean_ctor_get(v_a_1968_, 0);
v_fullRange_x3f_1971_ = lean_ctor_get(v_a_1968_, 1);
v_severity_x3f_1972_ = lean_ctor_get(v_a_1968_, 2);
v_isSilent_x3f_1973_ = lean_ctor_get(v_a_1968_, 3);
v_code_x3f_1974_ = lean_ctor_get(v_a_1968_, 4);
v_source_x3f_1975_ = lean_ctor_get(v_a_1968_, 5);
v_message_1976_ = lean_ctor_get(v_a_1968_, 6);
v_tags_x3f_1977_ = lean_ctor_get(v_a_1968_, 7);
v_leanTags_x3f_1978_ = lean_ctor_get(v_a_1968_, 8);
v_relatedInformation_x3f_1979_ = lean_ctor_get(v_a_1968_, 9);
v_data_x3f_1980_ = lean_ctor_get(v_a_1968_, 10);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_1982_ = v_a_1968_;
v_isShared_1983_ = v_isSharedCheck_2175_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_data_x3f_1980_);
lean_inc(v_relatedInformation_x3f_1979_);
lean_inc(v_leanTags_x3f_1978_);
lean_inc(v_tags_x3f_1977_);
lean_inc(v_message_1976_);
lean_inc(v_source_x3f_1975_);
lean_inc(v_code_x3f_1974_);
lean_inc(v_isSilent_x3f_1973_);
lean_inc(v_severity_x3f_1972_);
lean_inc(v_fullRange_x3f_1971_);
lean_inc(v_range_1970_);
lean_dec(v_a_1968_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2175_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v_fst_2012_; lean_object* v_snd_2013_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v_fst_2039_; lean_object* v_snd_2040_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_fst_2092_; lean_object* v_snd_2093_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v_fst_2108_; lean_object* v_snd_2109_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___y_2136_; lean_object* v_fst_2137_; lean_object* v_snd_2138_; lean_object* v___y_2151_; lean_object* v_fst_2152_; lean_object* v_snd_2153_; lean_object* v_fst_2156_; lean_object* v_snd_2157_; 
v___f_1984_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1985_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___f_1986_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_1987_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1970_);
if (lean_obj_tag(v_fullRange_x3f_1971_) == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_box(0);
v_fst_2156_ = v___x_2165_;
v_snd_2157_ = v_a_1969_;
goto v___jp_2155_;
}
else
{
lean_object* v_val_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2174_; 
v_val_2166_ = lean_ctor_get(v_fullRange_x3f_1971_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_fullRange_x3f_1971_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2168_ = v_fullRange_x3f_1971_;
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_val_2166_);
lean_dec(v_fullRange_x3f_1971_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_2166_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_fst_2156_ = v___x_2172_;
v_snd_2157_ = v_a_1969_;
goto v___jp_2155_;
}
}
}
v___jp_1988_:
{
lean_object* v___x_2000_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 9, v_fst_1997_);
lean_ctor_set(v___x_1982_, 8, v___y_1991_);
lean_ctor_set(v___x_1982_, 7, v___y_1990_);
lean_ctor_set(v___x_1982_, 6, v___y_1992_);
lean_ctor_set(v___x_1982_, 5, v___y_1994_);
lean_ctor_set(v___x_1982_, 4, v___y_1995_);
lean_ctor_set(v___x_1982_, 3, v___y_1993_);
lean_ctor_set(v___x_1982_, 2, v___y_1989_);
lean_ctor_set(v___x_1982_, 1, v___y_1996_);
lean_ctor_set(v___x_1982_, 0, v___x_1987_);
v___x_2000_ = v___x_1982_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___y_1996_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v___y_1989_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v___y_1993_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v___y_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 5, v___y_1994_);
lean_ctor_set(v_reuseFailAlloc_2003_, 6, v___y_1992_);
lean_ctor_set(v_reuseFailAlloc_2003_, 7, v___y_1990_);
lean_ctor_set(v_reuseFailAlloc_2003_, 8, v___y_1991_);
lean_ctor_set(v_reuseFailAlloc_2003_, 9, v_fst_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 10, v_data_x3f_1980_);
v___x_2000_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_57_(v___x_2000_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v_snd_1998_);
return v___x_2002_;
}
}
v___jp_2004_:
{
lean_object* v___x_2014_; 
v___x_2014_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_relatedInformation_x3f_1979_) == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_box(0);
v___y_1989_ = v___y_2005_;
v___y_1990_ = v___y_2006_;
v___y_1991_ = v_fst_2012_;
v___y_1992_ = v___y_2007_;
v___y_1993_ = v___y_2008_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2009_;
v___y_1996_ = v___y_2011_;
v_fst_1997_ = v___x_2015_;
v_snd_1998_ = v_snd_2013_;
goto v___jp_1988_;
}
else
{
lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2031_; 
v_val_2016_ = lean_ctor_get(v_relatedInformation_x3f_1979_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_relatedInformation_x3f_1979_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2018_ = v_relatedInformation_x3f_1979_;
v_isShared_2019_ = v_isSharedCheck_2031_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v_relatedInformation_x3f_1979_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2031_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
size_t v_sz_2020_; size_t v___x_2021_; lean_object* v___x_7261__overap_2022_; lean_object* v___x_2023_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v_sz_2020_ = lean_array_size(v_val_2016_);
v___x_2021_ = ((size_t)0ULL);
v___x_7261__overap_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2014_, v___f_1985_, v_sz_2020_, v___x_2021_, v_val_2016_);
v___x_2023_ = lean_apply_1(v___x_7261__overap_2022_, v_snd_2013_);
v_fst_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_fst_2024_);
v_snd_2025_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_snd_2025_);
lean_dec_ref(v___x_2023_);
v___x_2026_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2027_ = l_Array_toJson___redArg(v___x_2026_, v_fst_2024_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2027_);
v___x_2029_ = v___x_2018_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
v___y_1989_ = v___y_2005_;
v___y_1990_ = v___y_2006_;
v___y_1991_ = v_fst_2012_;
v___y_1992_ = v___y_2007_;
v___y_1993_ = v___y_2008_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2009_;
v___y_1996_ = v___y_2011_;
v_fst_1997_ = v___x_2029_;
v_snd_1998_ = v_snd_2025_;
goto v___jp_1988_;
}
}
}
}
v___jp_2032_:
{
lean_object* v___x_2041_; 
v___x_2041_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_leanTags_x3f_1978_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_box(0);
v___y_2005_ = v___y_2033_;
v___y_2006_ = v_fst_2039_;
v___y_2007_ = v___y_2034_;
v___y_2008_ = v___y_2035_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2036_;
v___y_2011_ = v___y_2038_;
v_fst_2012_ = v___x_2042_;
v_snd_2013_ = v_snd_2040_;
goto v___jp_2004_;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2058_; 
v_val_2043_ = lean_ctor_get(v_leanTags_x3f_1978_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_leanTags_x3f_1978_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2045_ = v_leanTags_x3f_1978_;
v_isShared_2046_ = v_isSharedCheck_2058_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_val_2043_);
lean_dec(v_leanTags_x3f_1978_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2058_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
size_t v_sz_2047_; size_t v___x_2048_; lean_object* v___x_7285__overap_2049_; lean_object* v___x_2050_; lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v_sz_2047_ = lean_array_size(v_val_2043_);
v___x_2048_ = ((size_t)0ULL);
v___x_7285__overap_2049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2041_, v___f_1984_, v_sz_2047_, v___x_2048_, v_val_2043_);
v___x_2050_ = lean_apply_1(v___x_7285__overap_2049_, v_snd_2040_);
v_fst_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_fst_2051_);
v_snd_2052_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_snd_2052_);
lean_dec_ref(v___x_2050_);
v___x_2053_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2054_ = l_Array_toJson___redArg(v___x_2053_, v_fst_2051_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2054_);
v___x_2056_ = v___x_2045_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v___y_2005_ = v___y_2033_;
v___y_2006_ = v_fst_2039_;
v___y_2007_ = v___y_2034_;
v___y_2008_ = v___y_2035_;
v___y_2009_ = v___y_2037_;
v___y_2010_ = v___y_2036_;
v___y_2011_ = v___y_2038_;
v_fst_2012_ = v___x_2056_;
v_snd_2013_ = v_snd_2052_;
goto v___jp_2004_;
}
}
}
}
v___jp_2059_:
{
lean_object* v_rpcEncode_2066_; lean_object* v___x_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; 
v_rpcEncode_2066_ = lean_ctor_get(v_inst_1967_, 0);
lean_inc_ref(v_rpcEncode_2066_);
lean_dec_ref(v_inst_1967_);
v___x_2067_ = lean_apply_2(v_rpcEncode_2066_, v_message_1976_, v_snd_2065_);
v_fst_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v___x_2067_);
v___x_2070_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__22_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
if (lean_obj_tag(v_tags_x3f_1977_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_box(0);
v___y_2033_ = v___y_2060_;
v___y_2034_ = v_fst_2068_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v_fst_2064_;
v___y_2037_ = v___y_2062_;
v___y_2038_ = v___y_2063_;
v_fst_2039_ = v___x_2071_;
v_snd_2040_ = v_snd_2069_;
goto v___jp_2032_;
}
else
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2087_; 
v_val_2072_ = lean_ctor_get(v_tags_x3f_1977_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_tags_x3f_1977_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2074_ = v_tags_x3f_1977_;
v_isShared_2075_ = v_isSharedCheck_2087_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v_tags_x3f_1977_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2087_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
size_t v_sz_2076_; size_t v___x_2077_; lean_object* v___x_7309__overap_2078_; lean_object* v___x_2079_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v_sz_2076_ = lean_array_size(v_val_2072_);
v___x_2077_ = ((size_t)0ULL);
v___x_7309__overap_2078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2070_, v___f_1986_, v_sz_2076_, v___x_2077_, v_val_2072_);
v___x_2079_ = lean_apply_1(v___x_7309__overap_2078_, v_snd_2069_);
v_fst_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_fst_2080_);
v_snd_2081_ = lean_ctor_get(v___x_2079_, 1);
lean_inc(v_snd_2081_);
lean_dec_ref(v___x_2079_);
v___x_2082_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__23_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2083_ = l_Array_toJson___redArg(v___x_2082_, v_fst_2080_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2083_);
v___x_2085_ = v___x_2074_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v___y_2033_ = v___y_2060_;
v___y_2034_ = v_fst_2068_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v_fst_2064_;
v___y_2037_ = v___y_2062_;
v___y_2038_ = v___y_2063_;
v_fst_2039_ = v___x_2085_;
v_snd_2040_ = v_snd_2081_;
goto v___jp_2032_;
}
}
}
}
v___jp_2088_:
{
if (lean_obj_tag(v_source_x3f_1975_) == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_box(0);
v___y_2060_ = v___y_2089_;
v___y_2061_ = v___y_2090_;
v___y_2062_ = v_fst_2092_;
v___y_2063_ = v___y_2091_;
v_fst_2064_ = v___x_2094_;
v_snd_2065_ = v_snd_2093_;
goto v___jp_2059_;
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_val_2095_ = lean_ctor_get(v_source_x3f_1975_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_source_x3f_1975_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v_source_x3f_1975_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_val_2095_);
lean_dec(v_source_x3f_1975_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_val_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v___y_2060_ = v___y_2089_;
v___y_2061_ = v___y_2090_;
v___y_2062_ = v_fst_2092_;
v___y_2063_ = v___y_2091_;
v_fst_2064_ = v___x_2101_;
v_snd_2065_ = v_snd_2093_;
goto v___jp_2059_;
}
}
}
}
v___jp_2104_:
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_fst_2108_);
v___y_2089_ = v___y_2105_;
v___y_2090_ = v___y_2106_;
v___y_2091_ = v___y_2107_;
v_fst_2092_ = v___x_2110_;
v_snd_2093_ = v_snd_2109_;
goto v___jp_2088_;
}
v___jp_2111_:
{
if (lean_obj_tag(v_code_x3f_1974_) == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_box(0);
v___y_2089_ = v___y_2112_;
v___y_2090_ = v_fst_2114_;
v___y_2091_ = v___y_2113_;
v_fst_2092_ = v___x_2116_;
v_snd_2093_ = v_snd_2115_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2117_; 
v_val_2117_ = lean_ctor_get(v_code_x3f_1974_, 0);
lean_inc(v_val_2117_);
lean_dec_ref(v_code_x3f_1974_);
if (lean_obj_tag(v_val_2117_) == 0)
{
lean_object* v_i_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
v_i_2118_ = lean_ctor_get(v_val_2117_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_val_2117_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v_val_2117_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_i_2118_);
lean_dec(v_val_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_JsonNumber_fromInt(v_i_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 2);
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
v___y_2105_ = v___y_2112_;
v___y_2106_ = v_fst_2114_;
v___y_2107_ = v___y_2113_;
v_fst_2108_ = v___x_2124_;
v_snd_2109_ = v_snd_2115_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v_s_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
v_s_2127_ = lean_ctor_get(v_val_2117_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_val_2117_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v_val_2117_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_s_2127_);
lean_dec(v_val_2117_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set_tag(v___x_2129_, 3);
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_s_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
v___y_2105_ = v___y_2112_;
v___y_2106_ = v_fst_2114_;
v___y_2107_ = v___y_2113_;
v_fst_2108_ = v___x_2132_;
v_snd_2109_ = v_snd_2115_;
goto v___jp_2104_;
}
}
}
}
}
v___jp_2135_:
{
if (lean_obj_tag(v_isSilent_x3f_1973_) == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_box(0);
v___y_2112_ = v_fst_2137_;
v___y_2113_ = v___y_2136_;
v_fst_2114_ = v___x_2139_;
v_snd_2115_ = v_snd_2138_;
goto v___jp_2111_;
}
else
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2149_; 
v_val_2140_ = lean_ctor_get(v_isSilent_x3f_1973_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_isSilent_x3f_1973_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2142_ = v_isSilent_x3f_1973_;
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v_isSilent_x3f_1973_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_alloc_ctor(1, 0, 1);
v___x_2145_ = lean_unbox(v_val_2140_);
lean_dec(v_val_2140_);
lean_ctor_set_uint8(v___x_2144_, 0, v___x_2145_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2144_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2144_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v___y_2112_ = v_fst_2137_;
v___y_2113_ = v___y_2136_;
v_fst_2114_ = v___x_2147_;
v_snd_2115_ = v_snd_2138_;
goto v___jp_2111_;
}
}
}
}
v___jp_2150_:
{
lean_object* v___x_2154_; 
lean_inc(v_fst_2152_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_fst_2152_);
v___y_2136_ = v___y_2151_;
v_fst_2137_ = v___x_2154_;
v_snd_2138_ = v_snd_2153_;
goto v___jp_2135_;
}
v___jp_2155_:
{
if (lean_obj_tag(v_severity_x3f_1972_) == 0)
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_box(0);
v___y_2136_ = v_fst_2156_;
v_fst_2137_ = v___x_2158_;
v_snd_2138_ = v_snd_2157_;
goto v___jp_2135_;
}
else
{
lean_object* v_val_2159_; uint8_t v___x_2160_; 
v_val_2159_ = lean_ctor_get(v_severity_x3f_1972_, 0);
lean_inc(v_val_2159_);
lean_dec_ref(v_severity_x3f_1972_);
v___x_2160_ = lean_unbox(v_val_2159_);
lean_dec(v_val_2159_);
switch(v___x_2160_)
{
case 0:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2151_ = v_fst_2156_;
v_fst_2152_ = v___x_2161_;
v_snd_2153_ = v_snd_2157_;
goto v___jp_2150_;
}
case 1:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___lam__0___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2151_ = v_fst_2156_;
v_fst_2152_ = v___x_2162_;
v_snd_2153_ = v_snd_2157_;
goto v___jp_2150_;
}
case 2:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__25_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2151_ = v_fst_2156_;
v_fst_2152_ = v___x_2163_;
v_snd_2153_ = v_snd_2157_;
goto v___jp_2150_;
}
default: 
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__27_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___y_2151_ = v_fst_2156_;
v_fst_2152_ = v___x_2164_;
v_snd_2153_ = v_snd_2157_;
goto v___jp_2150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2176_, lean_object* v_inst_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2177_, v_a_2178_, v_a_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2181_, lean_object* v___x_2182_, lean_object* v_j_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_10279__overap_2186_; lean_object* v___x_2187_; 
v___x_2185_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_j_2183_);
v___x_10279__overap_2186_ = l_MonadExcept_ofExcept___redArg(v___x_2181_, v___x_2182_, v___x_2185_);
lean_inc_ref(v___y_2184_);
v___x_2187_ = lean_apply_1(v___x_10279__overap_2186_, v___y_2184_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2188_, lean_object* v___x_2189_, lean_object* v_j_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2188_, v___x_2189_, v_j_2190_, v___y_2191_);
lean_dec_ref(v___y_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2202_, lean_object* v___x_2203_, lean_object* v_j_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Json_getNat_x3f(v_j_2204_);
if (lean_obj_tag(v___x_2210_) == 1)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_dec_eq(v_a_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = lean_unsigned_to_nat(2u);
v___x_2215_ = lean_nat_dec_eq(v_a_2211_, v___x_2214_);
lean_dec(v_a_2211_);
if (v___x_2215_ == 0)
{
goto v___jp_2206_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_10295__overap_2217_; lean_object* v___x_2218_; 
v___x_2216_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10295__overap_2217_ = l_MonadExcept_ofExcept___redArg(v___x_2202_, v___x_2203_, v___x_2216_);
lean_inc_ref(v___y_2205_);
v___x_2218_ = lean_apply_1(v___x_10295__overap_2217_, v___y_2205_);
return v___x_2218_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_10298__overap_2220_; lean_object* v___x_2221_; 
lean_dec(v_a_2211_);
v___x_2219_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10298__overap_2220_ = l_MonadExcept_ofExcept___redArg(v___x_2202_, v___x_2203_, v___x_2219_);
lean_inc_ref(v___y_2205_);
v___x_2221_ = lean_apply_1(v___x_10298__overap_2220_, v___y_2205_);
return v___x_2221_;
}
}
else
{
lean_dec_ref(v___x_2210_);
goto v___jp_2206_;
}
v___jp_2206_:
{
lean_object* v___x_2207_; lean_object* v___x_10286__overap_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10286__overap_2208_ = l_MonadExcept_ofExcept___redArg(v___x_2202_, v___x_2203_, v___x_2207_);
lean_inc_ref(v___y_2205_);
v___x_2209_ = lean_apply_1(v___x_10286__overap_2208_, v___y_2205_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_j_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2222_, v___x_2223_, v_j_2224_, v___y_2225_);
lean_dec_ref(v___y_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v___x_2236_, lean_object* v___x_2237_, lean_object* v_j_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Json_getNat_x3f(v_j_2238_);
if (lean_obj_tag(v___x_2244_) == 1)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_dec_eq(v_a_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(2u);
v___x_2249_ = lean_nat_dec_eq(v_a_2245_, v___x_2248_);
lean_dec(v_a_2245_);
if (v___x_2249_ == 0)
{
goto v___jp_2240_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_10314__overap_2251_; lean_object* v___x_2252_; 
v___x_2250_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10314__overap_2251_ = l_MonadExcept_ofExcept___redArg(v___x_2236_, v___x_2237_, v___x_2250_);
lean_inc_ref(v___y_2239_);
v___x_2252_ = lean_apply_1(v___x_10314__overap_2251_, v___y_2239_);
return v___x_2252_;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_10317__overap_2254_; lean_object* v___x_2255_; 
lean_dec(v_a_2245_);
v___x_2253_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10317__overap_2254_ = l_MonadExcept_ofExcept___redArg(v___x_2236_, v___x_2237_, v___x_2253_);
lean_inc_ref(v___y_2239_);
v___x_2255_ = lean_apply_1(v___x_10317__overap_2254_, v___y_2239_);
return v___x_2255_;
}
}
else
{
lean_dec_ref(v___x_2244_);
goto v___jp_2240_;
}
v___jp_2240_:
{
lean_object* v___x_2241_; lean_object* v___x_10305__overap_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_10305__overap_2242_ = l_MonadExcept_ofExcept___redArg(v___x_2236_, v___x_2237_, v___x_2241_);
lean_inc_ref(v___y_2239_);
v___x_2243_ = lean_apply_1(v___x_10305__overap_2242_, v___y_2239_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_j_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v___x_2256_, v___x_2257_, v_j_2258_, v___y_2259_);
lean_dec_ref(v___y_2259_);
return v_res_2260_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2262_ = l_ReaderT_instMonad___redArg(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___f_2264_; 
v___x_2263_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2264_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2264_, 0, v___x_2263_);
return v___f_2264_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___f_2266_; 
v___x_2265_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2266_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_2266_, 0, v___x_2265_);
return v___f_2266_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___f_2268_; 
v___x_2267_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2268_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_2268_, 0, v___x_2267_);
return v___f_2268_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___f_2270_; 
v___x_2269_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2270_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
return v___f_2270_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2272_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_2272_, 0, lean_box(0));
lean_closure_set(v___x_2272_, 1, lean_box(0));
lean_closure_set(v___x_2272_, 2, v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___f_2273_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2274_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__5_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___f_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2277_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_2277_, 0, lean_box(0));
lean_closure_set(v___x_2277_, 1, lean_box(0));
lean_closure_set(v___x_2277_, 2, v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___f_2278_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__4_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2279_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__3_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___f_2280_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2281_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__7_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2282_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__6_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2281_);
lean_ctor_set(v___x_2283_, 2, v___f_2280_);
lean_ctor_set(v___x_2283_, 3, v___f_2279_);
lean_ctor_set(v___x_2283_, 4, v___f_2278_);
return v___x_2283_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2285_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_2285_, 0, lean_box(0));
lean_closure_set(v___x_2285_, 1, lean_box(0));
lean_closure_set(v___x_2285_, 2, v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__9_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2287_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__8_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2290_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_2290_, 0, lean_box(0));
lean_closure_set(v___x_2290_, 1, lean_box(0));
lean_closure_set(v___x_2290_, 2, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_inst_2306_, lean_object* v_j_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveDiagnostic_3833933514____hygCtx___hyg_39_(v_j_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_inst_2306_);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2751_; 
v_a_2318_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2320_ = v___x_2309_;
v_isShared_2321_ = v_isSharedCheck_2751_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2309_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2751_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_toApplicative_2324_; lean_object* v_toPure_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_range_2330_; lean_object* v_fullRange_x3f_2331_; lean_object* v_severity_x3f_2332_; lean_object* v_isSilent_x3f_2333_; lean_object* v_code_x3f_2334_; lean_object* v_source_x3f_2335_; lean_object* v_message_2336_; lean_object* v_tags_x3f_2337_; lean_object* v_leanTags_x3f_2338_; lean_object* v_relatedInformation_x3f_2339_; lean_object* v_data_x3f_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2750_; 
v___x_2322_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2323_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__10_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v_toApplicative_2324_ = lean_ctor_get(v___x_2322_, 0);
v_toPure_2325_ = lean_ctor_get(v_toApplicative_2324_, 1);
lean_inc(v_toPure_2325_);
v___f_2326_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2326_, 0, v_toPure_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_, &l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2__once, _init_l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__11_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___f_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2328_);
v_range_2330_ = lean_ctor_get(v_a_2318_, 0);
v_fullRange_x3f_2331_ = lean_ctor_get(v_a_2318_, 1);
v_severity_x3f_2332_ = lean_ctor_get(v_a_2318_, 2);
v_isSilent_x3f_2333_ = lean_ctor_get(v_a_2318_, 3);
v_code_x3f_2334_ = lean_ctor_get(v_a_2318_, 4);
v_source_x3f_2335_ = lean_ctor_get(v_a_2318_, 5);
v_message_2336_ = lean_ctor_get(v_a_2318_, 6);
v_tags_x3f_2337_ = lean_ctor_get(v_a_2318_, 7);
v_leanTags_x3f_2338_ = lean_ctor_get(v_a_2318_, 8);
v_relatedInformation_x3f_2339_ = lean_ctor_get(v_a_2318_, 9);
v_data_x3f_2340_ = lean_ctor_get(v_a_2318_, 10);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_a_2318_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2342_ = v_a_2318_;
v_isShared_2343_ = v_isSharedCheck_2750_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_data_x3f_2340_);
lean_inc(v_relatedInformation_x3f_2339_);
lean_inc(v_leanTags_x3f_2338_);
lean_inc(v_tags_x3f_2337_);
lean_inc(v_message_2336_);
lean_inc(v_source_x3f_2335_);
lean_inc(v_code_x3f_2334_);
lean_inc(v_isSilent_x3f_2333_);
lean_inc(v_severity_x3f_2332_);
lean_inc(v_fullRange_x3f_2331_);
lean_inc(v_range_2330_);
lean_dec(v_a_2318_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2750_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_9531__overap_2345_; lean_object* v___x_2346_; 
v___x_2344_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_range_2330_);
lean_inc_ref(v___x_2329_);
v___x_9531__overap_2345_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2344_);
lean_inc_ref(v_a_2308_);
v___x_2346_ = lean_apply_1(v___x_9531__overap_2345_, v_a_2308_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec(v_source_x3f_2335_);
lean_dec(v_code_x3f_2334_);
lean_dec(v_isSilent_x3f_2333_);
lean_dec(v_severity_x3f_2332_);
lean_dec(v_fullRange_x3f_2331_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2749_; 
v_a_2355_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2357_ = v___x_2346_;
v_isShared_2358_ = v_isSharedCheck_2749_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2346_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2749_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v_____do__lift_2369_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v_____do__lift_2385_; lean_object* v___y_2386_; lean_object* v___f_2409_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v_____do__lift_2418_; lean_object* v___y_2419_; lean_object* v___f_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v_____do__lift_2461_; lean_object* v___y_2462_; lean_object* v___f_2496_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v_____do__lift_2502_; lean_object* v___y_2503_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v_____do__lift_2553_; lean_object* v___y_2554_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v_j_2597_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v_____do__lift_2610_; lean_object* v___y_2611_; lean_object* v___y_2650_; lean_object* v_____do__lift_2651_; lean_object* v___y_2652_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v_____do__lift_2702_; lean_object* v___y_2703_; 
lean_inc_ref_n(v___x_2329_, 3);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__0_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2409_, 0, v___x_2323_);
lean_closure_set(v___f_2409_, 1, v___x_2329_);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__1_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2453_, 0, v___x_2323_);
lean_closure_set(v___f_2453_, 1, v___x_2329_);
v___f_2496_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___lam__2_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___f_2496_, 0, v___x_2323_);
lean_closure_set(v___f_2496_, 1, v___x_2329_);
if (lean_obj_tag(v_fullRange_x3f_2331_) == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_box(0);
v_____do__lift_2702_ = v___x_2728_;
v___y_2703_ = v_a_2308_;
goto v___jp_2701_;
}
else
{
lean_object* v_val_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2748_; 
v_val_2729_ = lean_ctor_get(v_fullRange_x3f_2331_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_fullRange_x3f_2331_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2731_ = v_fullRange_x3f_2331_;
v_isShared_2732_ = v_isSharedCheck_2748_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_val_2729_);
lean_dec(v_fullRange_x3f_2331_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2748_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_9909__overap_2734_; lean_object* v___x_2735_; 
v___x_2733_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_val_2729_);
lean_inc_ref(v___x_2329_);
v___x_9909__overap_2734_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2733_);
lean_inc_ref(v_a_2308_);
v___x_2735_ = lean_apply_1(v___x_9909__overap_2734_, v_a_2308_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_del_object(v___x_2731_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec(v_source_x3f_2335_);
lean_dec(v_code_x3f_2334_);
lean_dec(v_isSilent_x3f_2333_);
lean_dec(v_severity_x3f_2332_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; 
v_a_2744_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2735_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_a_2744_);
v___x_2746_ = v___x_2731_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
v_____do__lift_2702_ = v___x_2746_;
v___y_2703_ = v_a_2308_;
goto v___jp_2701_;
}
}
}
}
v___jp_2359_:
{
lean_object* v___x_2371_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 10, v_____do__lift_2369_);
lean_ctor_set(v___x_2342_, 9, v___y_2361_);
lean_ctor_set(v___x_2342_, 8, v___y_2365_);
lean_ctor_set(v___x_2342_, 7, v___y_2363_);
lean_ctor_set(v___x_2342_, 6, v___y_2360_);
lean_ctor_set(v___x_2342_, 5, v___y_2362_);
lean_ctor_set(v___x_2342_, 4, v___y_2367_);
lean_ctor_set(v___x_2342_, 3, v___y_2364_);
lean_ctor_set(v___x_2342_, 2, v___y_2366_);
lean_ctor_set(v___x_2342_, 1, v___y_2368_);
lean_ctor_set(v___x_2342_, 0, v_a_2355_);
v___x_2371_ = v___x_2342_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2355_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___y_2368_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v___y_2366_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v___y_2364_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2375_, 5, v___y_2362_);
lean_ctor_set(v_reuseFailAlloc_2375_, 6, v___y_2360_);
lean_ctor_set(v_reuseFailAlloc_2375_, 7, v___y_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 8, v___y_2365_);
lean_ctor_set(v_reuseFailAlloc_2375_, 9, v___y_2361_);
lean_ctor_set(v_reuseFailAlloc_2375_, 10, v_____do__lift_2369_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2371_);
v___x_2373_ = v___x_2357_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
v___jp_2376_:
{
if (lean_obj_tag(v_data_x3f_2340_) == 0)
{
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v___y_2360_ = v___y_2377_;
v___y_2361_ = v_____do__lift_2385_;
v___y_2362_ = v___y_2378_;
v___y_2363_ = v___y_2379_;
v___y_2364_ = v___y_2380_;
v___y_2365_ = v___y_2382_;
v___y_2366_ = v___y_2381_;
v___y_2367_ = v___y_2384_;
v___y_2368_ = v___y_2383_;
v_____do__lift_2369_ = v_data_x3f_2340_;
goto v___jp_2359_;
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2408_; 
v_val_2387_ = lean_ctor_get(v_data_x3f_2340_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_data_x3f_2340_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2389_ = v_data_x3f_2340_;
v_isShared_2390_ = v_isSharedCheck_2408_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_val_2387_);
lean_dec(v_data_x3f_2340_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2408_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_val_2387_);
v___x_2392_ = v___x_2320_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_val_2387_);
v___x_2392_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_9963__overap_2393_; lean_object* v___x_2394_; 
v___x_9963__overap_2393_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2392_);
lean_inc_ref(v___y_2386_);
v___x_2394_ = lean_apply_1(v___x_9963__overap_2393_, v___y_2386_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_del_object(v___x_2389_);
lean_dec(v_____do__lift_2385_);
lean_dec(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; 
v_a_2403_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2394_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2403_);
v___x_2405_ = v___x_2389_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
v___y_2360_ = v___y_2377_;
v___y_2361_ = v_____do__lift_2385_;
v___y_2362_ = v___y_2378_;
v___y_2363_ = v___y_2379_;
v___y_2364_ = v___y_2380_;
v___y_2365_ = v___y_2382_;
v___y_2366_ = v___y_2381_;
v___y_2367_ = v___y_2384_;
v___y_2368_ = v___y_2383_;
v_____do__lift_2369_ = v___x_2405_;
goto v___jp_2359_;
}
}
}
}
}
}
v___jp_2410_:
{
if (lean_obj_tag(v_relatedInformation_x3f_2339_) == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v___f_2409_);
v___x_2420_ = lean_box(0);
v___y_2377_ = v___y_2411_;
v___y_2378_ = v___y_2412_;
v___y_2379_ = v___y_2413_;
v___y_2380_ = v___y_2414_;
v___y_2381_ = v___y_2415_;
v___y_2382_ = v_____do__lift_2418_;
v___y_2383_ = v___y_2417_;
v___y_2384_ = v___y_2416_;
v_____do__lift_2385_ = v___x_2420_;
v___y_2386_ = v___y_2419_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2452_; 
v_val_2421_ = lean_ctor_get(v_relatedInformation_x3f_2339_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_relatedInformation_x3f_2339_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2423_ = v_relatedInformation_x3f_2339_;
v_isShared_2424_ = v_isSharedCheck_2452_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v_relatedInformation_x3f_2339_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2452_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___f_2425_; lean_object* v___x_2426_; 
v___f_2425_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2426_ = l_Array_fromJson_x3f___redArg(v___f_2425_, v_val_2421_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2423_);
lean_dec(v_____do__lift_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2435_; size_t v_sz_2436_; size_t v___x_2437_; lean_object* v___x_10013__overap_2438_; lean_object* v___x_2439_; 
v_a_2435_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2426_);
v_sz_2436_ = lean_array_size(v_a_2435_);
v___x_2437_ = ((size_t)0ULL);
v___x_10013__overap_2438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2323_, v___f_2409_, v_sz_2436_, v___x_2437_, v_a_2435_);
lean_inc_ref(v___y_2419_);
v___x_2439_ = lean_apply_1(v___x_10013__overap_2438_, v___y_2419_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2423_);
lean_dec(v_____do__lift_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; 
v_a_2448_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2439_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_a_2448_);
v___x_2450_ = v___x_2423_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
v___y_2377_ = v___y_2411_;
v___y_2378_ = v___y_2412_;
v___y_2379_ = v___y_2413_;
v___y_2380_ = v___y_2414_;
v___y_2381_ = v___y_2415_;
v___y_2382_ = v_____do__lift_2418_;
v___y_2383_ = v___y_2417_;
v___y_2384_ = v___y_2416_;
v_____do__lift_2385_ = v___x_2450_;
v___y_2386_ = v___y_2419_;
goto v___jp_2376_;
}
}
}
}
}
}
v___jp_2454_:
{
if (lean_obj_tag(v_leanTags_x3f_2338_) == 0)
{
lean_object* v___x_2463_; 
lean_dec_ref(v___f_2453_);
v___x_2463_ = lean_box(0);
v___y_2411_ = v___y_2455_;
v___y_2412_ = v___y_2456_;
v___y_2413_ = v_____do__lift_2461_;
v___y_2414_ = v___y_2457_;
v___y_2415_ = v___y_2458_;
v___y_2416_ = v___y_2460_;
v___y_2417_ = v___y_2459_;
v_____do__lift_2418_ = v___x_2463_;
v___y_2419_ = v___y_2462_;
goto v___jp_2410_;
}
else
{
lean_object* v_val_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2495_; 
v_val_2464_ = lean_ctor_get(v_leanTags_x3f_2338_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_leanTags_x3f_2338_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2466_ = v_leanTags_x3f_2338_;
v_isShared_2467_ = v_isSharedCheck_2495_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_val_2464_);
lean_dec(v_leanTags_x3f_2338_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2495_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; 
v___f_2468_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2469_ = l_Array_fromJson_x3f___redArg(v___f_2468_, v_val_2464_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2466_);
lean_dec(v_____do__lift_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
lean_object* v_a_2478_; size_t v_sz_2479_; size_t v___x_2480_; lean_object* v___x_10062__overap_2481_; lean_object* v___x_2482_; 
v_a_2478_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2469_);
v_sz_2479_ = lean_array_size(v_a_2478_);
v___x_2480_ = ((size_t)0ULL);
v___x_10062__overap_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2323_, v___f_2453_, v_sz_2479_, v___x_2480_, v_a_2478_);
lean_inc_ref(v___y_2462_);
v___x_2482_ = lean_apply_1(v___x_10062__overap_2481_, v___y_2462_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_del_object(v___x_2466_);
lean_dec(v_____do__lift_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; 
v_a_2491_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2491_);
lean_dec_ref(v___x_2482_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v_a_2491_);
v___x_2493_ = v___x_2466_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v___y_2411_ = v___y_2455_;
v___y_2412_ = v___y_2456_;
v___y_2413_ = v_____do__lift_2461_;
v___y_2414_ = v___y_2457_;
v___y_2415_ = v___y_2458_;
v___y_2416_ = v___y_2460_;
v___y_2417_ = v___y_2459_;
v_____do__lift_2418_ = v___x_2493_;
v___y_2419_ = v___y_2462_;
goto v___jp_2410_;
}
}
}
}
}
}
v___jp_2497_:
{
lean_object* v_rpcDecode_2504_; lean_object* v___x_2505_; 
v_rpcDecode_2504_ = lean_ctor_get(v_inst_2306_, 1);
lean_inc_ref(v_rpcDecode_2504_);
lean_dec_ref(v_inst_2306_);
lean_inc_ref(v___y_2503_);
v___x_2505_ = lean_apply_2(v_rpcDecode_2504_, v_message_2336_, v___y_2503_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_____do__lift_2502_);
lean_dec(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
if (lean_obj_tag(v_tags_x3f_2337_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v___f_2496_);
v_a_2514_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2505_);
v___x_2515_ = lean_box(0);
v___y_2455_ = v_a_2514_;
v___y_2456_ = v_____do__lift_2502_;
v___y_2457_ = v___y_2498_;
v___y_2458_ = v___y_2499_;
v___y_2459_ = v___y_2501_;
v___y_2460_ = v___y_2500_;
v_____do__lift_2461_ = v___x_2515_;
v___y_2462_ = v___y_2503_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2516_; lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2548_; 
v_a_2516_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2505_);
v_val_2517_ = lean_ctor_get(v_tags_x3f_2337_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_tags_x3f_2337_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2519_ = v_tags_x3f_2337_;
v_isShared_2520_ = v_isSharedCheck_2548_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v_tags_x3f_2337_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2548_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___f_2521_; lean_object* v___x_2522_; 
v___f_2521_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__12_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2522_ = l_Array_fromJson_x3f___redArg(v___f_2521_, v_val_2517_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_del_object(v___x_2519_);
lean_dec(v_a_2516_);
lean_dec(v_____do__lift_2502_);
lean_dec(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_a_2531_; size_t v_sz_2532_; size_t v___x_2533_; lean_object* v___x_10111__overap_2534_; lean_object* v___x_2535_; 
v_a_2531_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2531_);
lean_dec_ref(v___x_2522_);
v_sz_2532_ = lean_array_size(v_a_2531_);
v___x_2533_ = ((size_t)0ULL);
v___x_10111__overap_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2323_, v___f_2496_, v_sz_2532_, v___x_2533_, v_a_2531_);
lean_inc_ref(v___y_2503_);
v___x_2535_ = lean_apply_1(v___x_10111__overap_2534_, v___y_2503_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_del_object(v___x_2519_);
lean_dec(v_a_2516_);
lean_dec(v_____do__lift_2502_);
lean_dec(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; 
v_a_2544_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2535_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v_a_2544_);
v___x_2546_ = v___x_2519_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
v___y_2455_ = v_a_2516_;
v___y_2456_ = v_____do__lift_2502_;
v___y_2457_ = v___y_2498_;
v___y_2458_ = v___y_2499_;
v___y_2459_ = v___y_2501_;
v___y_2460_ = v___y_2500_;
v_____do__lift_2461_ = v___x_2546_;
v___y_2462_ = v___y_2503_;
goto v___jp_2454_;
}
}
}
}
}
}
}
v___jp_2549_:
{
if (lean_obj_tag(v_source_x3f_2335_) == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
v___y_2498_ = v___y_2550_;
v___y_2499_ = v___y_2551_;
v___y_2500_ = v_____do__lift_2553_;
v___y_2501_ = v___y_2552_;
v_____do__lift_2502_ = v___x_2555_;
v___y_2503_ = v___y_2554_;
goto v___jp_2497_;
}
else
{
lean_object* v_val_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2575_; 
v_val_2556_ = lean_ctor_get(v_source_x3f_2335_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_source_x3f_2335_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2558_ = v_source_x3f_2335_;
v_isShared_2559_ = v_isSharedCheck_2575_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_val_2556_);
lean_dec(v_source_x3f_2335_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2575_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_9777__overap_2561_; lean_object* v___x_2562_; 
v___x_2560_ = l_Lean_Json_getStr_x3f(v_val_2556_);
lean_inc_ref(v___x_2329_);
v___x_9777__overap_2561_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2560_);
lean_inc_ref(v___y_2554_);
v___x_2562_ = lean_apply_1(v___x_9777__overap_2561_, v___y_2554_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_del_object(v___x_2558_);
lean_dec(v_____do__lift_2553_);
lean_dec(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2571_);
lean_dec_ref(v___x_2562_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v_a_2571_);
v___x_2573_ = v___x_2558_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
v___y_2498_ = v___y_2550_;
v___y_2499_ = v___y_2551_;
v___y_2500_ = v_____do__lift_2553_;
v___y_2501_ = v___y_2552_;
v_____do__lift_2502_ = v___x_2573_;
v___y_2503_ = v___y_2554_;
goto v___jp_2497_;
}
}
}
}
}
v___jp_2576_:
{
if (lean_obj_tag(v___y_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec(v_source_x3f_2335_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2582_ = lean_ctor_get(v___y_2581_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___y_2581_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___y_2581_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___y_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___y_2581_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___y_2581_);
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2590_);
v___y_2550_ = v___y_2577_;
v___y_2551_ = v___y_2578_;
v___y_2552_ = v___y_2579_;
v_____do__lift_2553_ = v___x_2591_;
v___y_2554_ = v___y_2580_;
goto v___jp_2549_;
}
}
v___jp_2592_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_9821__overap_2605_; lean_object* v___x_2606_; 
v___x_2598_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__13_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2599_ = lean_unsigned_to_nat(80u);
v___x_2600_ = l_Lean_Json_pretty(v_j_2597_, v___x_2599_);
v___x_2601_ = lean_string_append(v___x_2598_, v___x_2600_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2603_ = lean_string_append(v___x_2601_, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_inc_ref(v___x_2329_);
v___x_9821__overap_2605_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2604_);
lean_inc_ref(v___y_2596_);
v___x_2606_ = lean_apply_1(v___x_9821__overap_2605_, v___y_2596_);
v___y_2577_ = v___y_2593_;
v___y_2578_ = v___y_2594_;
v___y_2579_ = v___y_2595_;
v___y_2580_ = v___y_2596_;
v___y_2581_ = v___x_2606_;
goto v___jp_2576_;
}
v___jp_2607_:
{
if (lean_obj_tag(v_code_x3f_2334_) == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_box(0);
v___y_2550_ = v_____do__lift_2610_;
v___y_2551_ = v___y_2608_;
v___y_2552_ = v___y_2609_;
v_____do__lift_2553_ = v___x_2612_;
v___y_2554_ = v___y_2611_;
goto v___jp_2549_;
}
else
{
lean_object* v_val_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2648_; 
v_val_2613_ = lean_ctor_get(v_code_x3f_2334_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_code_x3f_2334_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2615_ = v_code_x3f_2334_;
v_isShared_2616_ = v_isSharedCheck_2648_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_val_2613_);
lean_dec(v_code_x3f_2334_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2648_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
switch(lean_obj_tag(v_val_2613_))
{
case 2:
{
lean_object* v_n_2617_; lean_object* v_mantissa_2618_; lean_object* v_exponent_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_n_2617_ = lean_ctor_get(v_val_2613_, 0);
v_mantissa_2618_ = lean_ctor_get(v_n_2617_, 0);
v_exponent_2619_ = lean_ctor_get(v_n_2617_, 1);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_nat_dec_eq(v_exponent_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_del_object(v___x_2615_);
v___y_2593_ = v_____do__lift_2610_;
v___y_2594_ = v___y_2608_;
v___y_2595_ = v___y_2609_;
v___y_2596_ = v___y_2611_;
v_j_2597_ = v_val_2613_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2633_; 
lean_inc(v_mantissa_2618_);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_val_2613_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v_val_2613_, 0);
lean_dec(v_unused_2634_);
v___x_2623_ = v_val_2613_;
v_isShared_2624_ = v_isSharedCheck_2633_;
goto v_resetjp_2622_;
}
else
{
lean_dec(v_val_2613_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2633_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 0);
lean_ctor_set(v___x_2623_, 0, v_mantissa_2618_);
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_mantissa_2618_);
v___x_2626_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2626_);
v___x_2628_ = v___x_2615_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_9829__overap_2629_; lean_object* v___x_2630_; 
lean_inc_ref(v___x_2329_);
v___x_9829__overap_2629_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2628_);
lean_inc_ref(v___y_2611_);
v___x_2630_ = lean_apply_1(v___x_9829__overap_2629_, v___y_2611_);
v___y_2577_ = v_____do__lift_2610_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___y_2609_;
v___y_2580_ = v___y_2611_;
v___y_2581_ = v___x_2630_;
goto v___jp_2576_;
}
}
}
}
}
case 3:
{
lean_object* v_s_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2647_; 
v_s_2635_ = lean_ctor_get(v_val_2613_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_val_2613_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2637_ = v_val_2613_;
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_s_2635_);
lean_dec(v_val_2613_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2647_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_s_2635_);
v___x_2640_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2640_);
v___x_2642_ = v___x_2615_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_9833__overap_2643_; lean_object* v___x_2644_; 
lean_inc_ref(v___x_2329_);
v___x_9833__overap_2643_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2642_);
lean_inc_ref(v___y_2611_);
v___x_2644_ = lean_apply_1(v___x_9833__overap_2643_, v___y_2611_);
v___y_2577_ = v_____do__lift_2610_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___y_2609_;
v___y_2580_ = v___y_2611_;
v___y_2581_ = v___x_2644_;
goto v___jp_2576_;
}
}
}
}
default: 
{
lean_del_object(v___x_2615_);
v___y_2593_ = v_____do__lift_2610_;
v___y_2594_ = v___y_2608_;
v___y_2595_ = v___y_2609_;
v___y_2596_ = v___y_2611_;
v_j_2597_ = v_val_2613_;
goto v___jp_2592_;
}
}
}
}
}
v___jp_2649_:
{
if (lean_obj_tag(v_isSilent_x3f_2333_) == 0)
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_box(0);
v___y_2608_ = v_____do__lift_2651_;
v___y_2609_ = v___y_2650_;
v_____do__lift_2610_ = v___x_2653_;
v___y_2611_ = v___y_2652_;
goto v___jp_2607_;
}
else
{
lean_object* v_val_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2673_; 
v_val_2654_ = lean_ctor_get(v_isSilent_x3f_2333_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_isSilent_x3f_2333_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2656_ = v_isSilent_x3f_2333_;
v_isShared_2657_ = v_isSharedCheck_2673_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_val_2654_);
lean_dec(v_isSilent_x3f_2333_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2673_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_9838__overap_2659_; lean_object* v___x_2660_; 
v___x_2658_ = l_Lean_Json_getBool_x3f(v_val_2654_);
lean_dec(v_val_2654_);
lean_inc_ref(v___x_2329_);
v___x_9838__overap_2659_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2658_);
lean_inc_ref(v___y_2652_);
v___x_2660_ = lean_apply_1(v___x_9838__overap_2659_, v___y_2652_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2656_);
lean_dec(v_____do__lift_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec(v_source_x3f_2335_);
lean_dec(v_code_x3f_2334_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; 
v_a_2669_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2660_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_a_2669_);
v___x_2671_ = v___x_2656_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
v___y_2608_ = v_____do__lift_2651_;
v___y_2609_ = v___y_2650_;
v_____do__lift_2610_ = v___x_2671_;
v___y_2611_ = v___y_2652_;
goto v___jp_2607_;
}
}
}
}
}
v___jp_2674_:
{
if (lean_obj_tag(v___y_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v___y_2676_);
lean_dec_ref(v___f_2496_);
lean_dec_ref(v___f_2453_);
lean_dec_ref(v___f_2409_);
lean_del_object(v___x_2357_);
lean_dec(v_a_2355_);
lean_del_object(v___x_2342_);
lean_dec(v_data_x3f_2340_);
lean_dec(v_relatedInformation_x3f_2339_);
lean_dec(v_leanTags_x3f_2338_);
lean_dec(v_tags_x3f_2337_);
lean_dec(v_message_2336_);
lean_dec(v_source_x3f_2335_);
lean_dec(v_code_x3f_2334_);
lean_dec(v_isSilent_x3f_2333_);
lean_dec_ref(v___x_2329_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_inst_2306_);
v_a_2678_ = lean_ctor_get(v___y_2677_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___y_2677_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___y_2677_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___y_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___y_2677_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v___y_2677_);
v___x_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_a_2686_);
v___y_2650_ = v___y_2676_;
v_____do__lift_2651_ = v___x_2687_;
v___y_2652_ = v___y_2675_;
goto v___jp_2649_;
}
}
v___jp_2688_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_9882__overap_2699_; lean_object* v___x_2700_; 
v___x_2692_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__14_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
v___x_2693_ = lean_unsigned_to_nat(80u);
v___x_2694_ = l_Lean_Json_pretty(v___y_2690_, v___x_2693_);
v___x_2695_ = lean_string_append(v___x_2692_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableMsgEmbed_dec_00___x40_Lean_Widget_InteractiveDiagnostic_1765450820____hygCtx___hyg_1__spec__4_spec__8___closed__1));
v___x_2697_ = lean_string_append(v___x_2695_, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_inc_ref(v___x_2329_);
v___x_9882__overap_2699_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2698_);
lean_inc_ref(v___y_2689_);
v___x_2700_ = lean_apply_1(v___x_9882__overap_2699_, v___y_2689_);
v___y_2675_ = v___y_2689_;
v___y_2676_ = v___y_2691_;
v___y_2677_ = v___x_2700_;
goto v___jp_2674_;
}
v___jp_2701_:
{
if (lean_obj_tag(v_severity_x3f_2332_) == 0)
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_box(0);
v___y_2650_ = v_____do__lift_2702_;
v_____do__lift_2651_ = v___x_2704_;
v___y_2652_ = v___y_2703_;
goto v___jp_2649_;
}
else
{
lean_object* v_val_2705_; lean_object* v___x_2706_; 
v_val_2705_ = lean_ctor_get(v_severity_x3f_2332_, 0);
lean_inc_n(v_val_2705_, 2);
lean_dec_ref(v_severity_x3f_2332_);
v___x_2706_ = l_Lean_Json_getNat_x3f(v_val_2705_);
if (lean_obj_tag(v___x_2706_) == 1)
{
lean_object* v_a_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref(v___x_2706_);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_dec_eq(v_a_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = lean_unsigned_to_nat(2u);
v___x_2711_ = lean_nat_dec_eq(v_a_2707_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = lean_unsigned_to_nat(3u);
v___x_2713_ = lean_nat_dec_eq(v_a_2707_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = lean_unsigned_to_nat(4u);
v___x_2715_ = lean_nat_dec_eq(v_a_2707_, v___x_2714_);
lean_dec(v_a_2707_);
if (v___x_2715_ == 0)
{
v___y_2689_ = v___y_2703_;
v___y_2690_ = v_val_2705_;
v___y_2691_ = v_____do__lift_2702_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_9895__overap_2717_; lean_object* v___x_2718_; 
lean_dec(v_val_2705_);
v___x_2716_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__15_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2329_);
v___x_9895__overap_2717_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2716_);
lean_inc_ref(v___y_2703_);
v___x_2718_ = lean_apply_1(v___x_9895__overap_2717_, v___y_2703_);
v___y_2675_ = v___y_2703_;
v___y_2676_ = v_____do__lift_2702_;
v___y_2677_ = v___x_2718_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2719_; lean_object* v___x_9898__overap_2720_; lean_object* v___x_2721_; 
lean_dec(v_a_2707_);
lean_dec(v_val_2705_);
v___x_2719_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__16_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2329_);
v___x_9898__overap_2720_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2719_);
lean_inc_ref(v___y_2703_);
v___x_2721_ = lean_apply_1(v___x_9898__overap_2720_, v___y_2703_);
v___y_2675_ = v___y_2703_;
v___y_2676_ = v_____do__lift_2702_;
v___y_2677_ = v___x_2721_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_9901__overap_2723_; lean_object* v___x_2724_; 
lean_dec(v_a_2707_);
lean_dec(v_val_2705_);
v___x_2722_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__17_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2329_);
v___x_9901__overap_2723_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2722_);
lean_inc_ref(v___y_2703_);
v___x_2724_ = lean_apply_1(v___x_9901__overap_2723_, v___y_2703_);
v___y_2675_ = v___y_2703_;
v___y_2676_ = v_____do__lift_2702_;
v___y_2677_ = v___x_2724_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_9904__overap_2726_; lean_object* v___x_2727_; 
lean_dec(v_a_2707_);
lean_dec(v_val_2705_);
v___x_2725_ = ((lean_object*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg___closed__18_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_));
lean_inc_ref(v___x_2329_);
v___x_9904__overap_2726_ = l_MonadExcept_ofExcept___redArg(v___x_2323_, v___x_2329_, v___x_2725_);
lean_inc_ref(v___y_2703_);
v___x_2727_ = lean_apply_1(v___x_9904__overap_2726_, v___y_2703_);
v___y_2675_ = v___y_2703_;
v___y_2676_ = v_____do__lift_2702_;
v___y_2677_ = v___x_2727_;
goto v___jp_2674_;
}
}
else
{
lean_dec_ref(v___x_2706_);
v___y_2689_ = v___y_2703_;
v___y_2690_ = v_val_2705_;
v___y_2691_ = v_____do__lift_2702_;
goto v___jp_2688_;
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
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_inst_2752_, lean_object* v_j_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2752_, v_j_2753_, v_a_2754_);
lean_dec_ref(v_a_2754_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(lean_object* v_00_u03b1_2756_, lean_object* v_inst_2757_, lean_object* v_j_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec___redArg_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_inst_2757_, v_j_2758_, v_a_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed(lean_object* v_00_u03b1_2761_, lean_object* v_inst_2762_, lean_object* v_j_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_(v_00_u03b1_2761_, v_inst_2762_, v_j_2763_, v_a_2764_);
lean_dec_ref(v_a_2764_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(lean_object* v_inst_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_inc_ref(v_inst_2766_);
v___x_2767_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_enc_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2_), 4, 2);
lean_closure_set(v___x_2767_, 0, lean_box(0));
lean_closure_set(v___x_2767_, 1, v_inst_2766_);
v___x_2768_ = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableDiagnosticWith_dec_00___x40_Lean_Widget_InteractiveDiagnostic_2989700264____hygCtx___hyg_2____boxed), 4, 2);
lean_closure_set(v___x_2768_, 0, lean_box(0));
lean_closure_set(v___x_2768_, 1, v_inst_2766_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith(lean_object* v_00_u03b1_2770_, lean_object* v_inst_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Widget_instRpcEncodableDiagnosticWith___redArg(v_inst_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
switch(lean_obj_tag(v_x_2776_))
{
case 0:
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2786_; 
v_a_2778_ = lean_ctor_get(v_x_2776_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2780_ = v_x_2776_;
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v_x_2776_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_a_2778_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
case 1:
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2798_; 
v_a_2787_ = lean_ctor_get(v_x_2776_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2789_ = v_x_2776_;
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v_x_2776_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2791_ = l_Lean_Widget_InteractiveGoal_pretty(v_a_2787_);
v___x_2792_ = l_Std_Format_defWidth;
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = l_Std_Format_pretty(v___x_2791_, v___x_2792_, v___x_2793_, v___x_2793_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2794_);
v___x_2796_ = v___x_2789_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
case 2:
{
lean_object* v_alt_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_alt_2799_ = lean_ctor_get(v_x_2776_, 1);
lean_inc_ref(v_alt_2799_);
lean_dec_ref(v_x_2776_);
v___x_2800_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_alt_2799_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
default: 
{
lean_object* v___x_2802_; 
lean_dec_ref(v_x_2776_);
v___x_2802_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___closed__1));
return v___x_2802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed(lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0(v_x_2803_, v_x_2804_);
lean_dec_ref(v_x_2804_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(lean_object* v_tt_2806_){
_start:
{
lean_object* v___f_2807_; lean_object* v_tt_2808_; lean_object* v___x_2809_; 
v___f_2807_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt___lam__0___boxed), 2, 0);
v_tt_2808_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_2807_, v_tt_2806_);
v___x_2809_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object* v_diag_2810_){
_start:
{
lean_object* v_range_2811_; lean_object* v_fullRange_x3f_2812_; lean_object* v_severity_x3f_2813_; lean_object* v_isSilent_x3f_2814_; lean_object* v_code_x3f_2815_; lean_object* v_source_x3f_2816_; lean_object* v_message_2817_; lean_object* v_tags_x3f_2818_; lean_object* v_leanTags_x3f_2819_; lean_object* v_relatedInformation_x3f_2820_; lean_object* v_data_x3f_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2829_; 
v_range_2811_ = lean_ctor_get(v_diag_2810_, 0);
v_fullRange_x3f_2812_ = lean_ctor_get(v_diag_2810_, 1);
v_severity_x3f_2813_ = lean_ctor_get(v_diag_2810_, 2);
v_isSilent_x3f_2814_ = lean_ctor_get(v_diag_2810_, 3);
v_code_x3f_2815_ = lean_ctor_get(v_diag_2810_, 4);
v_source_x3f_2816_ = lean_ctor_get(v_diag_2810_, 5);
v_message_2817_ = lean_ctor_get(v_diag_2810_, 6);
v_tags_x3f_2818_ = lean_ctor_get(v_diag_2810_, 7);
v_leanTags_x3f_2819_ = lean_ctor_get(v_diag_2810_, 8);
v_relatedInformation_x3f_2820_ = lean_ctor_get(v_diag_2810_, 9);
v_data_x3f_2821_ = lean_ctor_get(v_diag_2810_, 10);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_diag_2810_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2823_ = v_diag_2810_;
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_data_x3f_2821_);
lean_inc(v_relatedInformation_x3f_2820_);
lean_inc(v_leanTags_x3f_2819_);
lean_inc(v_tags_x3f_2818_);
lean_inc(v_message_2817_);
lean_inc(v_source_x3f_2816_);
lean_inc(v_code_x3f_2815_);
lean_inc(v_isSilent_x3f_2814_);
lean_inc(v_severity_x3f_2813_);
lean_inc(v_fullRange_x3f_2812_);
lean_inc(v_range_2811_);
lean_dec(v_diag_2810_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_InteractiveDiagnostic_toDiagnostic_prettyTt(v_message_2817_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 6, v___x_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_range_2811_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_fullRange_x3f_2812_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_severity_x3f_2813_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_isSilent_x3f_2814_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_code_x3f_2815_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_source_x3f_2816_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_tags_x3f_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_leanTags_x3f_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 9, v_relatedInformation_x3f_2820_);
lean_ctor_set(v_reuseFailAlloc_2828_, 10, v_data_x3f_2821_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(lean_object* v_nCtx_2830_, lean_object* v_ctx_2831_){
_start:
{
lean_object* v_env_2832_; lean_object* v_mctx_2833_; lean_object* v_lctx_2834_; lean_object* v_opts_2835_; lean_object* v_currNamespace_2836_; lean_object* v_openDecls_2837_; lean_object* v___x_2838_; 
v_env_2832_ = lean_ctor_get(v_ctx_2831_, 0);
v_mctx_2833_ = lean_ctor_get(v_ctx_2831_, 1);
v_lctx_2834_ = lean_ctor_get(v_ctx_2831_, 2);
v_opts_2835_ = lean_ctor_get(v_ctx_2831_, 3);
v_currNamespace_2836_ = lean_ctor_get(v_nCtx_2830_, 0);
v_openDecls_2837_ = lean_ctor_get(v_nCtx_2830_, 1);
lean_inc(v_openDecls_2837_);
lean_inc(v_currNamespace_2836_);
lean_inc_ref(v_opts_2835_);
lean_inc_ref(v_lctx_2834_);
lean_inc_ref(v_mctx_2833_);
lean_inc_ref(v_env_2832_);
v___x_2838_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2838_, 0, v_env_2832_);
lean_ctor_set(v___x_2838_, 1, v_mctx_2833_);
lean_ctor_set(v___x_2838_, 2, v_lctx_2834_);
lean_ctor_set(v___x_2838_, 3, v_opts_2835_);
lean_ctor_set(v___x_2838_, 4, v_currNamespace_2836_);
lean_ctor_set(v___x_2838_, 5, v_openDecls_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext___boxed(lean_object* v_nCtx_2839_, lean_object* v_ctx_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_2839_, v_ctx_2840_);
lean_dec_ref(v_ctx_2840_);
lean_dec_ref(v_nCtx_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx(lean_object* v_x_2842_){
_start:
{
switch(lean_obj_tag(v_x_2842_))
{
case 0:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_unsigned_to_nat(0u);
return v___x_2843_;
}
case 1:
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_unsigned_to_nat(1u);
return v___x_2844_;
}
case 2:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_unsigned_to_nat(2u);
return v___x_2845_;
}
case 3:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_unsigned_to_nat(3u);
return v___x_2846_;
}
default: 
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_unsigned_to_nat(4u);
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx___boxed(lean_object* v_x_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_EmbedFmt_ctorIdx(v_x_2848_);
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
lean_dec_ref(v_t_2850_);
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
lean_dec_ref(v_t_2850_);
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
v___x_2917_ = l_Array_instInhabited(lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(lean_object* v_e_2927_, lean_object* v_a_2928_){
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
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed___boxed(lean_object* v_e_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v_e_2934_, v_a_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(lean_object* v_fmt_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2960_; 
v___x_2941_ = lean_box(4);
v___x_2942_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_2941_, v_a_2939_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2960_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2960_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2959_; 
v_fst_2947_ = lean_ctor_get(v_a_2943_, 0);
v_snd_2948_ = lean_ctor_get(v_a_2943_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_a_2943_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2950_ = v_a_2943_;
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snd_2948_);
lean_inc(v_fst_2947_);
lean_dec(v_a_2943_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_fst_2947_);
lean_ctor_set(v___x_2952_, 1, v_fmt_2938_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_snd_2948_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2954_);
v___x_2956_ = v___x_2945_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags___boxed(lean_object* v_fmt_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_2961_, v_a_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(lean_object* v_nCtx_2973_, lean_object* v_ctx_2974_){
_start:
{
lean_object* v_env_2975_; lean_object* v_mctx_2976_; lean_object* v_opts_2977_; lean_object* v_currNamespace_2978_; lean_object* v_openDecls_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_env_2975_ = lean_ctor_get(v_ctx_2974_, 0);
v_mctx_2976_ = lean_ctor_get(v_ctx_2974_, 1);
v_opts_2977_ = lean_ctor_get(v_ctx_2974_, 3);
v_currNamespace_2978_ = lean_ctor_get(v_nCtx_2973_, 0);
v_openDecls_2979_ = lean_ctor_get(v_nCtx_2973_, 1);
v___x_2980_ = lean_box(0);
v___x_2981_ = l_Lean_instInhabitedFileMap_default;
v___x_2982_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__2));
lean_inc(v_openDecls_2979_);
lean_inc(v_currNamespace_2978_);
lean_inc_ref(v_opts_2977_);
lean_inc_ref(v_mctx_2976_);
lean_inc_ref(v_env_2975_);
v___x_2983_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2983_, 0, v_env_2975_);
lean_ctor_set(v___x_2983_, 1, v___x_2980_);
lean_ctor_set(v___x_2983_, 2, v___x_2981_);
lean_ctor_set(v___x_2983_, 3, v_mctx_2976_);
lean_ctor_set(v___x_2983_, 4, v_opts_2977_);
lean_ctor_set(v___x_2983_, 5, v_currNamespace_2978_);
lean_ctor_set(v___x_2983_, 6, v_openDecls_2979_);
lean_ctor_set(v___x_2983_, 7, v___x_2982_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___closed__3));
v___x_2985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2980_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo___boxed(lean_object* v_nCtx_2986_, lean_object* v_ctx_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_2986_, v_ctx_2987_);
lean_dec_ref(v_ctx_2987_);
lean_dec_ref(v_nCtx_2986_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(lean_object* v_a_2989_, lean_object* v_b_2990_){
_start:
{
lean_object* v_array_2991_; lean_object* v_start_2992_; lean_object* v_stop_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3006_; 
v_array_2991_ = lean_ctor_get(v_a_2989_, 0);
v_start_2992_ = lean_ctor_get(v_a_2989_, 1);
v_stop_2993_ = lean_ctor_get(v_a_2989_, 2);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_a_2989_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2995_ = v_a_2989_;
v_isShared_2996_ = v_isSharedCheck_3006_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_stop_2993_);
lean_inc(v_start_2992_);
lean_inc(v_array_2991_);
lean_dec(v_a_2989_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3006_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_nat_dec_lt(v_start_2992_, v_stop_2993_);
if (v___x_2997_ == 0)
{
lean_del_object(v___x_2995_);
lean_dec(v_stop_2993_);
lean_dec(v_start_2992_);
lean_dec_ref(v_array_2991_);
return v_b_2990_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_nat_add(v_start_2992_, v___x_2998_);
lean_inc_ref(v_array_2991_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_2999_);
v___x_3001_ = v___x_2995_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_array_2991_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_stop_2993_);
v___x_3001_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_array_fget(v_array_2991_, v_start_2992_);
lean_dec(v_start_2992_);
lean_dec_ref(v_array_2991_);
v___x_3003_ = lean_array_push(v_b_2990_, v___x_3002_);
v_a_2989_ = v___x_3001_;
v_b_2990_ = v___x_3003_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1(void){
_start:
{
lean_object* v___x_3009_; double v___x_3010_; 
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_float_of_nat(v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(lean_object* v_cls_3015_, lean_object* v_blockSize_3016_, lean_object* v_children_3017_){
_start:
{
lean_object* v___x_3018_; uint8_t v___y_3020_; uint8_t v___x_3042_; 
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_nat_dec_lt(v___x_3018_, v_blockSize_3016_);
if (v___x_3042_ == 0)
{
v___y_3020_ = v___x_3042_;
goto v___jp_3019_;
}
else
{
lean_object* v_start_3043_; lean_object* v_stop_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v_start_3043_ = lean_ctor_get(v_children_3017_, 1);
v_stop_3044_ = lean_ctor_get(v_children_3017_, 2);
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_add(v_blockSize_3016_, v___x_3045_);
v___x_3047_ = lean_nat_sub(v_stop_3044_, v_start_3043_);
v___x_3048_ = lean_nat_dec_lt(v___x_3046_, v___x_3047_);
lean_dec(v___x_3047_);
lean_dec(v___x_3046_);
v___y_3020_ = v___x_3048_;
goto v___jp_3019_;
}
v___jp_3019_:
{
if (v___y_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_dec(v_cls_3015_);
v___x_3021_ = l_Subarray_copy___redArg(v_children_3017_);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; lean_object* v_more_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; double v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_start_3029_; lean_object* v_stop_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_inc_ref(v_children_3017_);
v___x_3022_ = l_Subarray_drop___redArg(v_children_3017_, v_blockSize_3016_);
lean_inc(v_cls_3015_);
v_more_3023_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3015_, v_blockSize_3016_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__0));
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3027_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__2));
v___x_3028_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3028_, 0, v_cls_3015_);
lean_ctor_set(v___x_3028_, 1, v___x_3025_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
lean_ctor_set_float(v___x_3028_, sizeof(void*)*3, v___x_3026_);
lean_ctor_set_float(v___x_3028_, sizeof(void*)*3 + 8, v___x_3026_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*3 + 16, v___y_3020_);
v_start_3029_ = lean_ctor_get(v_children_3017_, 1);
lean_inc(v_start_3029_);
v_stop_3030_ = lean_ctor_get(v_children_3017_, 2);
lean_inc(v_stop_3030_);
v___x_3031_ = l_Subarray_take___redArg(v_children_3017_, v_blockSize_3016_);
v___x_3032_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v___x_3031_, v___x_3024_);
v___x_3033_ = lean_nat_sub(v_stop_3030_, v_start_3029_);
lean_dec(v_start_3029_);
lean_dec(v_stop_3030_);
v___x_3034_ = lean_nat_sub(v___x_3033_, v_blockSize_3016_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Nat_reprFast(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
v___x_3037_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__4));
v___x_3038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = l_Lean_MessageData_ofFormat(v___x_3038_);
v___x_3040_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3028_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_ctor_set(v___x_3040_, 2, v_more_3023_);
v___x_3041_ = lean_array_push(v___x_3032_, v___x_3040_);
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___boxed(lean_object* v_cls_3049_, lean_object* v_blockSize_3050_, lean_object* v_children_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v_cls_3049_, v_blockSize_3050_, v_children_3051_);
lean_dec(v_blockSize_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0(lean_object* v_inst_3053_, lean_object* v_R_3054_, lean_object* v_a_3055_, lean_object* v_b_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren_spec__0___redArg(v_a_3055_, v_b_3056_);
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
lean_dec_ref(v_val_3064_);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__3(lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_nat_to_int(v_a_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(lean_object* v_ctx_3079_, lean_object* v_nCtx_3080_, size_t v_sz_3081_, size_t v_i_3082_, lean_object* v_bs_3083_){
_start:
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_usize_dec_lt(v_i_3082_, v_sz_3081_);
if (v___x_3084_ == 0)
{
lean_dec_ref(v_nCtx_3080_);
return v_bs_3083_;
}
else
{
lean_object* v_v_3085_; lean_object* v___x_3086_; lean_object* v_bs_x27_3087_; lean_object* v___y_3089_; 
v_v_3085_ = lean_array_uget(v_bs_3083_, v_i_3082_);
v___x_3086_ = lean_unsigned_to_nat(0u);
v_bs_x27_3087_ = lean_array_uset(v_bs_3083_, v_i_3082_, v___x_3086_);
if (lean_obj_tag(v_ctx_3079_) == 0)
{
lean_object* v___x_3094_; 
lean_inc_ref(v_nCtx_3080_);
v___x_3094_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_nCtx_3080_);
lean_ctor_set(v___x_3094_, 1, v_v_3085_);
v___y_3089_ = v___x_3094_;
goto v___jp_3088_;
}
else
{
lean_object* v_val_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_val_3095_ = lean_ctor_get(v_ctx_3079_, 0);
lean_inc(v_val_3095_);
v___x_3096_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3096_, 0, v_val_3095_);
lean_ctor_set(v___x_3096_, 1, v_v_3085_);
lean_inc_ref(v_nCtx_3080_);
v___x_3097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_nCtx_3080_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___y_3089_ = v___x_3097_;
goto v___jp_3088_;
}
v___jp_3088_:
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)1ULL);
v___x_3091_ = lean_usize_add(v_i_3082_, v___x_3090_);
v___x_3092_ = lean_array_uset(v_bs_x27_3087_, v_i_3082_, v___y_3089_);
v_i_3082_ = v___x_3091_;
v_bs_3083_ = v___x_3092_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1___boxed(lean_object* v_ctx_3098_, lean_object* v_nCtx_3099_, lean_object* v_sz_3100_, lean_object* v_i_3101_, lean_object* v_bs_3102_){
_start:
{
size_t v_sz_boxed_3103_; size_t v_i_boxed_3104_; lean_object* v_res_3105_; 
v_sz_boxed_3103_ = lean_unbox_usize(v_sz_3100_);
lean_dec(v_sz_3100_);
v_i_boxed_3104_ = lean_unbox_usize(v_i_3101_);
lean_dec(v_i_3101_);
v_res_3105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v_ctx_3098_, v_nCtx_3099_, v_sz_boxed_3103_, v_i_boxed_3104_, v_bs_3102_);
lean_dec(v_ctx_3098_);
return v_res_3105_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_unsigned_to_nat(4u);
v___x_3113_ = lean_nat_to_int(v___x_3112_);
return v___x_3113_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__5));
v___x_3116_ = lean_mk_io_user_error(v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(lean_object* v_nCtx_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_ctx_3126_; lean_object* v_n_3127_; lean_object* v_d_3128_; lean_object* v___y_3129_; uint8_t v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v_nodes_3154_; lean_object* v___y_3155_; lean_object* v___y_3186_; uint8_t v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3221_; lean_object* v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; lean_object* v_header_3248_; lean_object* v___y_3249_; lean_object* v___y_3254_; lean_object* v___y_3255_; double v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; lean_object* v___y_3260_; double v___y_3261_; lean_object* v___y_3262_; lean_object* v_ctx_3272_; lean_object* v_data_3273_; lean_object* v_header_3274_; lean_object* v_children_3275_; lean_object* v___y_3276_; lean_object* v_ctx_3327_; lean_object* v_wi_3328_; lean_object* v_d_3329_; lean_object* v___y_3330_; lean_object* v_ctx_3371_; lean_object* v_d_3372_; lean_object* v___y_3373_; lean_object* v_ctx_3377_; lean_object* v_d_u2081_3378_; lean_object* v_d_u2082_3379_; lean_object* v___y_3380_; lean_object* v_ctx_3411_; lean_object* v_d_3412_; lean_object* v___y_3413_; lean_object* v___x_3434_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; 
v___x_3434_ = l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_;
if (lean_obj_tag(v_a_3121_) == 0)
{
switch(lean_obj_tag(v_a_3122_))
{
case 0:
{
lean_object* v_a_3446_; lean_object* v_fmt_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v_nCtx_3120_);
v_a_3446_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3446_);
lean_dec_ref(v_a_3122_);
v_fmt_3447_ = lean_ctor_get(v_a_3446_, 0);
lean_inc(v_fmt_3447_);
lean_dec_ref(v_a_3446_);
v___x_3448_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_withIgnoreTags(v_fmt_3447_, v_a_3123_);
return v___x_3448_;
}
case 1:
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_nCtx_3120_);
v_a_3449_ = lean_ctor_get(v_a_3122_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3122_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3451_ = v_a_3122_;
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v_a_3122_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3453_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__8));
v___x_3454_ = l_Lean_mkMVar(v_a_3449_);
v___x_3455_ = lean_expr_dbg_to_string(v___x_3454_);
lean_dec_ref(v___x_3454_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 3);
lean_ctor_set(v___x_3451_, 0, v___x_3455_);
v___x_3457_ = v___x_3451_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3453_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_a_3123_);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
}
case 2:
{
lean_object* v_a_3463_; lean_object* v_a_3464_; 
v_a_3463_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3463_);
v_a_3464_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3464_);
lean_dec_ref(v_a_3122_);
v_ctx_3327_ = v_a_3121_;
v_wi_3328_ = v_a_3463_;
v_d_3329_ = v_a_3464_;
v___y_3330_ = v_a_3123_;
goto v___jp_3326_;
}
case 3:
{
lean_object* v_a_3465_; lean_object* v_a_3466_; 
v_a_3465_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3465_);
v_a_3466_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3466_);
lean_dec_ref(v_a_3122_);
v_ctx_3371_ = v_a_3465_;
v_d_3372_ = v_a_3466_;
v___y_3373_ = v_a_3123_;
goto v___jp_3370_;
}
case 4:
{
lean_object* v_a_3467_; lean_object* v_a_3468_; 
lean_dec_ref(v_nCtx_3120_);
v_a_3467_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3467_);
v_a_3468_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3468_);
lean_dec_ref(v_a_3122_);
v_nCtx_3120_ = v_a_3467_;
v_a_3122_ = v_a_3468_;
goto _start;
}
case 5:
{
lean_object* v_a_3470_; lean_object* v_a_3471_; 
v_a_3470_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_a_3470_);
v_a_3471_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3471_);
lean_dec_ref(v_a_3122_);
v_ctx_3126_ = v_a_3121_;
v_n_3127_ = v_a_3470_;
v_d_3128_ = v_a_3471_;
v___y_3129_ = v_a_3123_;
goto v___jp_3125_;
}
case 6:
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3472_);
lean_dec_ref(v_a_3122_);
v_ctx_3411_ = v_a_3121_;
v_d_3412_ = v_a_3472_;
v___y_3413_ = v_a_3123_;
goto v___jp_3410_;
}
case 7:
{
lean_object* v_a_3473_; lean_object* v_a_3474_; 
v_a_3473_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3473_);
v_a_3474_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3474_);
lean_dec_ref(v_a_3122_);
v_ctx_3377_ = v_a_3121_;
v_d_u2081_3378_ = v_a_3473_;
v_d_u2082_3379_ = v_a_3474_;
v___y_3380_ = v_a_3123_;
goto v___jp_3376_;
}
case 8:
{
lean_object* v_a_3475_; 
v_a_3475_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3475_);
lean_dec_ref(v_a_3122_);
v_a_3122_ = v_a_3475_;
goto _start;
}
case 9:
{
lean_object* v_data_3477_; lean_object* v_msg_3478_; lean_object* v_children_3479_; 
v_data_3477_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_data_3477_);
v_msg_3478_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_msg_3478_);
v_children_3479_ = lean_ctor_get(v_a_3122_, 2);
lean_inc_ref(v_children_3479_);
lean_dec_ref(v_a_3122_);
v_ctx_3272_ = v_a_3121_;
v_data_3273_ = v_data_3477_;
v_header_3274_ = v_msg_3478_;
v_children_3275_ = v_children_3479_;
v___y_3276_ = v_a_3123_;
goto v___jp_3271_;
}
default: 
{
lean_object* v_f_3480_; lean_object* v___x_3481_; 
v_f_3480_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_f_3480_);
lean_dec_ref(v_a_3122_);
v___x_3481_ = lean_box(0);
v___y_3436_ = v_a_3121_;
v___y_3437_ = v_f_3480_;
v___y_3438_ = v_a_3123_;
v___y_3439_ = v___x_3481_;
goto v___jp_3435_;
}
}
}
else
{
switch(lean_obj_tag(v_a_3122_))
{
case 0:
{
lean_object* v_a_3482_; lean_object* v_val_3483_; lean_object* v_fmt_3484_; lean_object* v_infos_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3520_; 
v_a_3482_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3482_);
lean_dec_ref(v_a_3122_);
v_val_3483_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_val_3483_);
lean_dec_ref(v_a_3121_);
v_fmt_3484_ = lean_ctor_get(v_a_3482_, 0);
v_infos_3485_ = lean_ctor_get(v_a_3482_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3487_ = v_a_3482_;
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_infos_3485_);
lean_inc(v_fmt_3484_);
lean_dec(v_a_3482_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3520_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3120_, v_val_3483_);
lean_dec(v_val_3483_);
lean_dec_ref(v_nCtx_3120_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_infos_3485_);
v___x_3491_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3491_, v_a_3123_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3510_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3510_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3510_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3509_; 
v_fst_3497_ = lean_ctor_get(v_a_3493_, 0);
v_snd_3498_ = lean_ctor_get(v_a_3493_, 1);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3493_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3500_ = v_a_3493_;
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_a_3493_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_fst_3497_);
lean_ctor_set(v___x_3502_, 1, v_fmt_3484_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3504_ = v___x_3500_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_snd_3498_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3504_);
v___x_3506_ = v___x_3495_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
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
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_fmt_3484_);
v_a_3511_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3492_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3492_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
case 1:
{
lean_object* v_val_3521_; lean_object* v_a_3522_; lean_object* v_lctx_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_val_3521_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_val_3521_);
lean_dec_ref(v_a_3121_);
v_a_3522_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v_a_3122_);
v_lctx_3523_ = lean_ctor_get(v_val_3521_, 2);
lean_inc_ref(v_lctx_3523_);
v___x_3524_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_mkContextInfo(v_nCtx_3120_, v_val_3521_);
lean_dec(v_val_3521_);
lean_dec_ref(v_nCtx_3120_);
v___x_3525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v_lctx_3523_);
lean_ctor_set(v___x_3525_, 2, v_a_3522_);
v___x_3526_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3525_, v_a_3123_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3545_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3545_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3545_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_fst_3531_; lean_object* v_snd_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3544_; 
v_fst_3531_ = lean_ctor_get(v_a_3527_, 0);
v_snd_3532_ = lean_ctor_get(v_a_3527_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3527_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3534_ = v_a_3527_;
v_isShared_3535_ = v_isSharedCheck_3544_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_snd_3532_);
lean_inc(v_fst_3531_);
lean_dec(v_a_3527_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3544_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_fst_3531_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3537_);
v___x_3539_ = v___x_3534_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_snd_3532_);
v___x_3539_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3539_);
v___x_3541_ = v___x_3529_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_a_3546_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3526_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3526_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
case 2:
{
lean_object* v_a_3554_; lean_object* v_a_3555_; 
v_a_3554_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3554_);
v_a_3555_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3555_);
lean_dec_ref(v_a_3122_);
v_ctx_3327_ = v_a_3121_;
v_wi_3328_ = v_a_3554_;
v_d_3329_ = v_a_3555_;
v___y_3330_ = v_a_3123_;
goto v___jp_3326_;
}
case 3:
{
lean_object* v_a_3556_; lean_object* v_a_3557_; 
lean_dec_ref(v_a_3121_);
v_a_3556_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3556_);
v_a_3557_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3557_);
lean_dec_ref(v_a_3122_);
v_ctx_3371_ = v_a_3556_;
v_d_3372_ = v_a_3557_;
v___y_3373_ = v_a_3123_;
goto v___jp_3370_;
}
case 4:
{
lean_object* v_a_3558_; lean_object* v_a_3559_; 
lean_dec_ref(v_nCtx_3120_);
v_a_3558_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3558_);
v_a_3559_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3559_);
lean_dec_ref(v_a_3122_);
v_nCtx_3120_ = v_a_3558_;
v_a_3122_ = v_a_3559_;
goto _start;
}
case 5:
{
lean_object* v_a_3561_; lean_object* v_a_3562_; 
v_a_3561_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_a_3561_);
v_a_3562_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3562_);
lean_dec_ref(v_a_3122_);
v_ctx_3126_ = v_a_3121_;
v_n_3127_ = v_a_3561_;
v_d_3128_ = v_a_3562_;
v___y_3129_ = v_a_3123_;
goto v___jp_3125_;
}
case 6:
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3563_);
lean_dec_ref(v_a_3122_);
v_ctx_3411_ = v_a_3121_;
v_d_3412_ = v_a_3563_;
v___y_3413_ = v_a_3123_;
goto v___jp_3410_;
}
case 7:
{
lean_object* v_a_3564_; lean_object* v_a_3565_; 
v_a_3564_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_a_3564_);
v_a_3565_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3565_);
lean_dec_ref(v_a_3122_);
v_ctx_3377_ = v_a_3121_;
v_d_u2081_3378_ = v_a_3564_;
v_d_u2082_3379_ = v_a_3565_;
v___y_3380_ = v_a_3123_;
goto v___jp_3376_;
}
case 8:
{
lean_object* v_a_3566_; 
v_a_3566_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_a_3566_);
lean_dec_ref(v_a_3122_);
v_a_3122_ = v_a_3566_;
goto _start;
}
case 9:
{
lean_object* v_data_3568_; lean_object* v_msg_3569_; lean_object* v_children_3570_; 
v_data_3568_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_data_3568_);
v_msg_3569_ = lean_ctor_get(v_a_3122_, 1);
lean_inc_ref(v_msg_3569_);
v_children_3570_ = lean_ctor_get(v_a_3122_, 2);
lean_inc_ref(v_children_3570_);
lean_dec_ref(v_a_3122_);
v_ctx_3272_ = v_a_3121_;
v_data_3273_ = v_data_3568_;
v_header_3274_ = v_msg_3569_;
v_children_3275_ = v_children_3570_;
v___y_3276_ = v_a_3123_;
goto v___jp_3271_;
}
default: 
{
lean_object* v_val_3571_; lean_object* v_f_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_val_3571_ = lean_ctor_get(v_a_3121_, 0);
v_f_3572_ = lean_ctor_get(v_a_3122_, 0);
lean_inc_ref(v_f_3572_);
lean_dec_ref(v_a_3122_);
v___x_3573_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_mkPPContext(v_nCtx_3120_, v_val_3571_);
v___x_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
v___y_3436_ = v_a_3121_;
v___y_3437_ = v_f_3572_;
v___y_3438_ = v_a_3123_;
v___y_3439_ = v___x_3574_;
goto v___jp_3435_;
}
}
}
v___jp_3125_:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3126_, v_d_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3149_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3149_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v_fst_3135_; lean_object* v_snd_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3148_; 
v_fst_3135_ = lean_ctor_get(v_a_3131_, 0);
v_snd_3136_ = lean_ctor_get(v_a_3131_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_a_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3138_ = v_a_3131_;
v_isShared_3139_ = v_isSharedCheck_3148_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_snd_3136_);
lean_inc(v_fst_3135_);
lean_dec(v_a_3131_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3148_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3140_ = lean_nat_to_int(v_n_3127_);
v___x_3141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v_fst_3135_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3141_);
v___x_3143_ = v___x_3138_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_snd_3136_);
v___x_3143_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3143_);
v___x_3145_ = v___x_3133_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
else
{
lean_dec(v_n_3127_);
return v___x_3130_;
}
}
v___jp_3150_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3156_, 0, v___y_3153_);
lean_ctor_set(v___x_3156_, 1, v___y_3152_);
lean_ctor_set(v___x_3156_, 2, v_nodes_3154_);
lean_ctor_set_uint8(v___x_3156_, sizeof(void*)*3, v___y_3151_);
v___x_3157_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3156_, v___y_3155_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3176_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3176_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3176_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; lean_object* v_snd_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3175_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
v_snd_3163_ = lean_ctor_get(v_a_3158_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3158_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3165_ = v_a_3158_;
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_snd_3163_);
lean_inc(v_fst_3162_);
lean_dec(v_a_3158_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3175_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_fst_3162_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3168_);
v___x_3170_ = v___x_3165_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_snd_3163_);
v___x_3170_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3172_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3170_);
v___x_3172_ = v___x_3160_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3157_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3157_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
v___jp_3185_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_array_get_size(v___y_3188_);
v___x_3194_ = l_Array_toSubarray___redArg(v___y_3188_, v___x_3192_, v___x_3193_);
lean_inc(v___y_3190_);
v___x_3195_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren(v___y_3190_, v___y_3191_, v___x_3194_);
lean_dec(v___y_3191_);
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
v___y_3151_ = v___y_3187_;
v___y_3152_ = v___y_3189_;
v___y_3153_ = v___y_3190_;
v_nodes_3154_ = v___x_3196_;
v___y_3155_ = v___y_3186_;
goto v___jp_3150_;
}
v___jp_3197_:
{
lean_object* v___x_3203_; lean_object* v_defValue_3204_; 
v___x_3203_ = l_Lean_MessageData_maxTraceChildren;
v_defValue_3204_ = lean_ctor_get(v___x_3203_, 1);
lean_inc(v_defValue_3204_);
v___y_3186_ = v___y_3198_;
v___y_3187_ = v___y_3200_;
v___y_3188_ = v___y_3199_;
v___y_3189_ = v___y_3201_;
v___y_3190_ = v___y_3202_;
v___y_3191_ = v_defValue_3204_;
goto v___jp_3185_;
}
v___jp_3205_:
{
size_t v_sz_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v_sz_3212_ = lean_array_size(v___y_3210_);
v___x_3213_ = ((size_t)0ULL);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__1(v___y_3207_, v_nCtx_3120_, v_sz_3212_, v___x_3213_, v___y_3210_);
if (lean_obj_tag(v___y_3207_) == 0)
{
v___y_3198_ = v___y_3206_;
v___y_3199_ = v___x_3214_;
v___y_3200_ = v___y_3208_;
v___y_3201_ = v___y_3209_;
v___y_3202_ = v___y_3211_;
goto v___jp_3197_;
}
else
{
lean_object* v_val_3215_; lean_object* v_opts_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_val_3215_ = lean_ctor_get(v___y_3207_, 0);
lean_inc(v_val_3215_);
lean_dec_ref(v___y_3207_);
v_opts_3216_ = lean_ctor_get(v_val_3215_, 3);
lean_inc_ref(v_opts_3216_);
lean_dec(v_val_3215_);
v___x_3217_ = l_Lean_MessageData_maxTraceChildren;
v___x_3218_ = l_Lean_Option_get_x3f___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__2(v_opts_3216_, v___x_3217_);
lean_dec_ref(v_opts_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
v___y_3198_ = v___y_3206_;
v___y_3199_ = v___x_3214_;
v___y_3200_ = v___y_3208_;
v___y_3201_ = v___y_3209_;
v___y_3202_ = v___y_3211_;
goto v___jp_3197_;
}
else
{
lean_object* v_val_3219_; 
v_val_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3219_);
lean_dec_ref(v___x_3218_);
v___y_3186_ = v___y_3206_;
v___y_3187_ = v___y_3208_;
v___y_3188_ = v___x_3214_;
v___y_3189_ = v___y_3209_;
v___y_3190_ = v___y_3211_;
v___y_3191_ = v_val_3219_;
goto v___jp_3185_;
}
}
}
v___jp_3220_:
{
size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v_sz_3227_ = lean_array_size(v___y_3225_);
v___x_3228_ = ((size_t)0ULL);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3120_, v___y_3222_, v_sz_3227_, v___x_3228_, v___y_3225_, v___y_3221_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v_fst_3231_; lean_object* v_snd_3232_; lean_object* v___x_3233_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
v_fst_3231_ = lean_ctor_get(v_a_3230_, 0);
lean_inc(v_fst_3231_);
v_snd_3232_ = lean_ctor_get(v_a_3230_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_a_3230_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v_fst_3231_);
v___y_3151_ = v___y_3223_;
v___y_3152_ = v___y_3224_;
v___y_3153_ = v___y_3226_;
v_nodes_3154_ = v___x_3233_;
v___y_3155_ = v_snd_3232_;
goto v___jp_3150_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v___y_3226_);
lean_dec(v___y_3224_);
v_a_3234_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3229_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3229_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
v___jp_3242_:
{
if (v___y_3244_ == 0)
{
v___y_3221_ = v___y_3249_;
v___y_3222_ = v___y_3243_;
v___y_3223_ = v___y_3244_;
v___y_3224_ = v_header_3248_;
v___y_3225_ = v___y_3245_;
v___y_3226_ = v___y_3247_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3250_ = lean_array_get_size(v___y_3245_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_nat_dec_eq(v___x_3250_, v___x_3251_);
if (v___x_3252_ == 0)
{
v___y_3206_ = v___y_3249_;
v___y_3207_ = v___y_3243_;
v___y_3208_ = v___y_3244_;
v___y_3209_ = v_header_3248_;
v___y_3210_ = v___y_3245_;
v___y_3211_ = v___y_3247_;
goto v___jp_3205_;
}
else
{
if (v___y_3246_ == 0)
{
v___y_3221_ = v___y_3249_;
v___y_3222_ = v___y_3243_;
v___y_3223_ = v___y_3244_;
v___y_3224_ = v_header_3248_;
v___y_3225_ = v___y_3245_;
v___y_3226_ = v___y_3247_;
goto v___jp_3220_;
}
else
{
v___y_3206_ = v___y_3249_;
v___y_3207_ = v___y_3243_;
v___y_3208_ = v___y_3244_;
v___y_3209_ = v_header_3248_;
v___y_3210_ = v___y_3245_;
v___y_3211_ = v___y_3247_;
goto v___jp_3205_;
}
}
}
}
v___jp_3253_:
{
lean_object* v___x_3263_; double v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3263_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__1));
v___x_3264_ = lean_float_sub(v___y_3256_, v___y_3261_);
v___x_3265_ = lean_float_to_string(v___x_3264_);
v___x_3266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3263_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__3));
v___x_3269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
lean_ctor_set(v___x_3270_, 1, v___y_3260_);
v___y_3243_ = v___y_3255_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___y_3258_;
v___y_3246_ = v___y_3259_;
v___y_3247_ = v___y_3262_;
v_header_3248_ = v___x_3270_;
v___y_3249_ = v___y_3254_;
goto v___jp_3242_;
}
v___jp_3271_:
{
lean_object* v_cls_3277_; double v_startTime_3278_; double v_stopTime_3279_; uint8_t v_collapsed_3280_; uint8_t v___x_3281_; 
v_cls_3277_ = lean_ctor_get(v_data_3273_, 0);
lean_inc(v_cls_3277_);
v_startTime_3278_ = lean_ctor_get_float(v_data_3273_, sizeof(void*)*3);
v_stopTime_3279_ = lean_ctor_get_float(v_data_3273_, sizeof(void*)*3 + 8);
v_collapsed_3280_ = lean_ctor_get_uint8(v_data_3273_, sizeof(void*)*3 + 16);
lean_dec_ref(v_data_3273_);
v___x_3281_ = l_Lean_Name_isAnonymous(v_cls_3277_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
lean_inc(v_ctx_3272_);
lean_inc_ref(v_nCtx_3120_);
v___x_3282_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3272_, v_header_3274_, v___y_3276_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v_fst_3284_; lean_object* v_snd_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3295_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref(v___x_3282_);
v_fst_3284_ = lean_ctor_get(v_a_3283_, 0);
v_snd_3285_ = lean_ctor_get(v_a_3283_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_a_3283_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3287_ = v_a_3283_;
v_isShared_3288_ = v_isSharedCheck_3295_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_snd_3285_);
lean_inc(v_fst_3284_);
lean_dec(v_a_3283_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3295_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__4);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 4);
lean_ctor_set(v___x_3287_, 1, v_fst_3284_);
lean_ctor_set(v___x_3287_, 0, v___x_3289_);
v___x_3291_ = v___x_3287_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_fst_3284_);
v___x_3291_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
double v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = lean_float_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_chopUpChildren___closed__1);
v___x_3293_ = lean_float_beq(v_startTime_3278_, v___x_3292_);
if (v___x_3293_ == 0)
{
v___y_3254_ = v_snd_3285_;
v___y_3255_ = v_ctx_3272_;
v___y_3256_ = v_stopTime_3279_;
v___y_3257_ = v_collapsed_3280_;
v___y_3258_ = v_children_3275_;
v___y_3259_ = v___x_3281_;
v___y_3260_ = v___x_3291_;
v___y_3261_ = v_startTime_3278_;
v___y_3262_ = v_cls_3277_;
goto v___jp_3253_;
}
else
{
if (v___x_3281_ == 0)
{
v___y_3243_ = v_ctx_3272_;
v___y_3244_ = v_collapsed_3280_;
v___y_3245_ = v_children_3275_;
v___y_3246_ = v___x_3281_;
v___y_3247_ = v_cls_3277_;
v_header_3248_ = v___x_3291_;
v___y_3249_ = v_snd_3285_;
goto v___jp_3242_;
}
else
{
v___y_3254_ = v_snd_3285_;
v___y_3255_ = v_ctx_3272_;
v___y_3256_ = v_stopTime_3279_;
v___y_3257_ = v_collapsed_3280_;
v___y_3258_ = v_children_3275_;
v___y_3259_ = v___x_3281_;
v___y_3260_ = v___x_3291_;
v___y_3261_ = v_startTime_3278_;
v___y_3262_ = v_cls_3277_;
goto v___jp_3253_;
}
}
}
}
}
else
{
lean_dec(v_cls_3277_);
lean_dec_ref(v_children_3275_);
lean_dec(v_ctx_3272_);
lean_dec_ref(v_nCtx_3120_);
return v___x_3282_;
}
}
else
{
size_t v_sz_3296_; size_t v___x_3297_; lean_object* v___x_3298_; 
lean_dec(v_cls_3277_);
lean_dec_ref(v_header_3274_);
v_sz_3296_ = lean_array_size(v_children_3275_);
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3120_, v_ctx_3272_, v_sz_3296_, v___x_3297_, v_children_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3317_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3317_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3317_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
v_fst_3303_ = lean_ctor_get(v_a_3299_, 0);
v_snd_3304_ = lean_ctor_get(v_a_3299_, 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_a_3299_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3306_ = v_a_3299_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_snd_3304_);
lean_inc(v_fst_3303_);
lean_dec(v_a_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3308_ = lean_array_to_list(v_fst_3303_);
v___x_3309_ = l_Std_Format_join(v___x_3308_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3309_);
v___x_3311_ = v___x_3306_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_snd_3304_);
v___x_3311_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3311_);
v___x_3313_ = v___x_3301_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
v_a_3318_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3298_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3298_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
v___jp_3326_:
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3327_, v_d_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3369_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
v_fst_3333_ = lean_ctor_get(v_a_3332_, 0);
v_snd_3334_ = lean_ctor_get(v_a_3332_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3332_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3336_ = v_a_3332_;
v_isShared_3337_ = v_isSharedCheck_3369_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3334_);
lean_inc(v_fst_3333_);
lean_dec(v_a_3332_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3369_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 2);
lean_ctor_set(v___x_3336_, 1, v_fst_3333_);
lean_ctor_set(v___x_3336_, 0, v_wi_3328_);
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_wi_3328_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_fst_3333_);
v___x_3339_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_pushEmbed(v___x_3339_, v_snd_3334_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3359_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3359_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3359_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_fst_3345_; lean_object* v_snd_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3358_; 
v_fst_3345_ = lean_ctor_get(v_a_3341_, 0);
v_snd_3346_ = lean_ctor_get(v_a_3341_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_a_3341_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3348_ = v_a_3341_;
v_isShared_3349_ = v_isSharedCheck_3358_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_snd_3346_);
lean_inc(v_fst_3345_);
lean_dec(v_a_3341_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3358_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_fst_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_snd_3346_);
v___x_3353_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3355_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v___x_3353_);
v___x_3355_ = v___x_3343_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
v_a_3360_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3340_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3340_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_wi_3328_);
return v___x_3331_;
}
}
v___jp_3370_:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_ctx_3371_);
v_a_3121_ = v___x_3374_;
v_a_3122_ = v_d_3372_;
v_a_3123_ = v___y_3373_;
goto _start;
}
v___jp_3376_:
{
lean_object* v___x_3381_; 
lean_inc(v_ctx_3377_);
lean_inc_ref(v_nCtx_3120_);
v___x_3381_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3377_, v_d_u2081_3378_, v___y_3380_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v_fst_3383_; lean_object* v_snd_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3409_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v_fst_3383_ = lean_ctor_get(v_a_3382_, 0);
v_snd_3384_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3386_ = v_a_3382_;
v_isShared_3387_ = v_isSharedCheck_3409_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_snd_3384_);
lean_inc(v_fst_3383_);
lean_dec(v_a_3382_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3409_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; 
v___x_3388_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3377_, v_d_u2082_3379_, v_snd_3384_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3408_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3408_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3408_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3407_; 
v_fst_3393_ = lean_ctor_get(v_a_3389_, 0);
v_snd_3394_ = lean_ctor_get(v_a_3389_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3389_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3396_ = v_a_3389_;
v_isShared_3397_ = v_isSharedCheck_3407_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3393_);
lean_dec(v_a_3389_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3407_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 5);
lean_ctor_set(v___x_3386_, 1, v_fst_3393_);
v___x_3399_ = v___x_3386_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_fst_3383_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_fst_3393_);
v___x_3399_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3399_);
v___x_3401_ = v___x_3396_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_snd_3394_);
v___x_3401_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3401_);
v___x_3403_ = v___x_3391_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3386_);
lean_dec(v_fst_3383_);
return v___x_3388_;
}
}
}
else
{
lean_dec_ref(v_d_u2082_3379_);
lean_dec(v_ctx_3377_);
lean_dec_ref(v_nCtx_3120_);
return v___x_3381_;
}
}
v___jp_3410_:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3120_, v_ctx_3411_, v_d_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3433_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3433_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3433_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3432_; 
v_fst_3419_ = lean_ctor_get(v_a_3415_, 0);
v_snd_3420_ = lean_ctor_get(v_a_3415_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_a_3415_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3422_ = v_a_3415_;
v_isShared_3423_ = v_isSharedCheck_3432_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3419_);
lean_dec(v_a_3415_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3432_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
uint8_t v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = 0;
v___x_3425_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3425_, 0, v_fst_3419_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*1, v___x_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_snd_3420_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3427_);
v___x_3429_ = v___x_3417_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
return v___x_3414_;
}
}
v___jp_3435_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_apply_2(v___y_3437_, v___y_3439_, lean_box(0));
v___x_3441_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_3440_, v___x_3434_);
lean_dec(v___x_3440_);
if (lean_obj_tag(v___x_3441_) == 1)
{
lean_object* v_val_3442_; 
v_val_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_val_3442_);
lean_dec_ref(v___x_3441_);
v_a_3121_ = v___y_3436_;
v_a_3122_ = v_val_3442_;
v_a_3123_ = v___y_3438_;
goto _start;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v___x_3441_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3436_);
lean_dec_ref(v_nCtx_3120_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___closed__6);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(lean_object* v_nCtx_3575_, lean_object* v_ctx_3576_, size_t v_sz_3577_, size_t v_i_3578_, lean_object* v_bs_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_lt(v_i_3578_, v_sz_3577_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v_ctx_3576_);
lean_dec_ref(v_nCtx_3575_);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v_bs_3579_);
lean_ctor_set(v___x_3583_, 1, v___y_3580_);
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
else
{
lean_object* v_v_3585_; lean_object* v___x_3586_; 
v_v_3585_ = lean_array_uget_borrowed(v_bs_3579_, v_i_3578_);
lean_inc(v_v_3585_);
lean_inc(v_ctx_3576_);
lean_inc_ref(v_nCtx_3575_);
v___x_3586_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3575_, v_ctx_3576_, v_v_3585_, v___y_3580_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v___x_3590_; lean_object* v_bs_x27_3591_; size_t v___x_3592_; size_t v___x_3593_; lean_object* v___x_3594_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
v_fst_3588_ = lean_ctor_get(v_a_3587_, 0);
lean_inc(v_fst_3588_);
v_snd_3589_ = lean_ctor_get(v_a_3587_, 1);
lean_inc(v_snd_3589_);
lean_dec(v_a_3587_);
v___x_3590_ = lean_unsigned_to_nat(0u);
v_bs_x27_3591_ = lean_array_uset(v_bs_3579_, v_i_3578_, v___x_3590_);
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3578_, v___x_3592_);
v___x_3594_ = lean_array_uset(v_bs_x27_3591_, v_i_3578_, v_fst_3588_);
v_i_3578_ = v___x_3593_;
v_bs_3579_ = v___x_3594_;
v___y_3580_ = v_snd_3589_;
goto _start;
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec_ref(v_bs_3579_);
lean_dec(v_ctx_3576_);
lean_dec_ref(v_nCtx_3575_);
v_a_3596_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3586_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3586_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0___boxed(lean_object* v_nCtx_3604_, lean_object* v_ctx_3605_, lean_object* v_sz_3606_, lean_object* v_i_3607_, lean_object* v_bs_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
size_t v_sz_boxed_3611_; size_t v_i_boxed_3612_; lean_object* v_res_3613_; 
v_sz_boxed_3611_ = lean_unbox_usize(v_sz_3606_);
lean_dec(v_sz_3606_);
v_i_boxed_3612_ = lean_unbox_usize(v_i_3607_);
lean_dec(v_i_3607_);
v_res_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go_spec__0(v_nCtx_3604_, v_ctx_3605_, v_sz_boxed_3611_, v_i_boxed_3612_, v_bs_3608_, v___y_3609_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go___boxed(lean_object* v_nCtx_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v_nCtx_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(lean_object* v_msgData_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3627_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__0));
v___x_3628_ = lean_box(0);
v___x_3629_ = ((lean_object*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___closed__1));
v___x_3630_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux_go(v___x_3627_, v___x_3628_, v_msgData_3625_, v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux___boxed(lean_object* v_msgData_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3631_);
return v_res_3633_;
}
}
static lean_object* _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Widget_instInhabitedTaggedText_default(lean_box(0));
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(lean_object* v_g_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Widget_goalToInteractive(v_g_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3652_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_a_3642_);
v___x_3647_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
v___x_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3648_);
v___x_3650_ = v___x_3644_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3641_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3641_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed(lean_object* v_g_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0(v_g_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(lean_object* v_f_3668_, size_t v_sz_3669_, size_t v_i_3670_, lean_object* v_bs_3671_){
_start:
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_usize_dec_lt(v_i_3670_, v_sz_3669_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec_ref(v_f_3668_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v_bs_3671_);
return v___x_3674_;
}
else
{
lean_object* v_v_3675_; lean_object* v___x_3676_; 
v_v_3675_ = lean_array_uget_borrowed(v_bs_3671_, v_i_3670_);
lean_inc(v_v_3675_);
lean_inc_ref(v_f_3668_);
v___x_3676_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3668_, v_v_3675_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; lean_object* v_bs_x27_3679_; size_t v___x_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v_bs_x27_3679_ = lean_array_uset(v_bs_3671_, v_i_3670_, v___x_3678_);
v___x_3680_ = ((size_t)1ULL);
v___x_3681_ = lean_usize_add(v_i_3670_, v___x_3680_);
v___x_3682_ = lean_array_uset(v_bs_x27_3679_, v_i_3670_, v_a_3677_);
v_i_3670_ = v___x_3681_;
v_bs_3671_ = v___x_3682_;
goto _start;
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v_bs_3671_);
lean_dec_ref(v_f_3668_);
v_a_3684_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3676_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3676_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(lean_object* v_f_3692_, lean_object* v_x_3693_){
_start:
{
switch(lean_obj_tag(v_x_3693_))
{
case 0:
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_f_3692_);
v_a_3695_ = lean_ctor_get(v_x_3693_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_x_3693_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3697_ = v_x_3693_;
v_isShared_3698_ = v_isSharedCheck_3703_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v_x_3693_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3703_;
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
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
}
case 1:
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3730_; 
v_a_3704_ = lean_ctor_get(v_x_3693_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_x_3693_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3706_ = v_x_3693_;
v_isShared_3707_ = v_isSharedCheck_3730_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v_x_3693_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3730_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
size_t v_sz_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v_sz_3708_ = lean_array_size(v_a_3704_);
v___x_3709_ = ((size_t)0ULL);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3692_, v_sz_3708_, v___x_3709_, v_a_3704_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3721_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3713_ = v___x_3710_;
v_isShared_3714_ = v_isSharedCheck_3721_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3710_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3721_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v_a_3711_);
v___x_3716_ = v___x_3706_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3716_);
v___x_3718_ = v___x_3713_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_del_object(v___x_3706_);
v_a_3722_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3710_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3710_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
default: 
{
lean_object* v_a_3731_; lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3731_ = lean_ctor_get(v_x_3693_, 0);
lean_inc(v_a_3731_);
v_a_3732_ = lean_ctor_get(v_x_3693_, 1);
lean_inc_ref(v_a_3732_);
lean_dec_ref(v_x_3693_);
v___x_3733_ = lean_apply_3(v_f_3692_, v_a_3731_, v_a_3732_, lean_box(0));
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg___boxed(lean_object* v_f_3734_, lean_object* v_x_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3734_, v_x_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg___boxed(lean_object* v_f_3738_, lean_object* v_sz_3739_, lean_object* v_i_3740_, lean_object* v_bs_3741_, lean_object* v___y_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3739_);
lean_dec(v_sz_3739_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3740_);
lean_dec(v_i_3740_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3738_, v_sz_boxed_3743_, v_i_boxed_3744_, v_bs_3741_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_bs_3748_){
_start:
{
uint8_t v___x_3750_; 
v___x_3750_ = lean_usize_dec_lt(v_i_3747_, v_sz_3746_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v_bs_3748_);
return v___x_3751_;
}
else
{
lean_object* v_v_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v_bs_x27_3755_; size_t v___x_3756_; size_t v___x_3757_; lean_object* v___x_3758_; 
v_v_3752_ = lean_array_uget_borrowed(v_bs_3748_, v_i_3747_);
lean_inc(v_v_3752_);
v___x_3753_ = l_Lean_Server_WithRpcRef_mk___redArg(v_v_3752_);
v___x_3754_ = lean_unsigned_to_nat(0u);
v_bs_x27_3755_ = lean_array_uset(v_bs_3748_, v_i_3747_, v___x_3754_);
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_add(v_i_3747_, v___x_3756_);
v___x_3758_ = lean_array_uset(v_bs_x27_3755_, v_i_3747_, v___x_3753_);
v_i_3747_ = v___x_3757_;
v_bs_3748_ = v___x_3758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1___boxed(lean_object* v_sz_3760_, lean_object* v_i_3761_, lean_object* v_bs_3762_, lean_object* v___y_3763_){
_start:
{
size_t v_sz_boxed_3764_; size_t v_i_boxed_3765_; lean_object* v_res_3766_; 
v_sz_boxed_3764_ = lean_unbox_usize(v_sz_3760_);
lean_dec(v_sz_3760_);
v_i_boxed_3765_ = lean_unbox_usize(v_i_3761_);
lean_dec(v_i_3761_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_boxed_3764_, v_i_boxed_3765_, v_bs_3762_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(lean_object* v_col_3767_, lean_object* v_embeds_3768_, size_t v_sz_3769_, size_t v_i_3770_, lean_object* v_bs_3771_){
_start:
{
uint8_t v___x_3773_; 
v___x_3773_ = lean_usize_dec_lt(v_i_3770_, v_sz_3769_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v_embeds_3768_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_bs_3771_);
return v___x_3774_;
}
else
{
lean_object* v_v_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_v_3775_ = lean_array_uget_borrowed(v_bs_3771_, v_i_3770_);
v___x_3776_ = lean_unsigned_to_nat(2u);
v___x_3777_ = lean_nat_add(v_col_3767_, v___x_3776_);
lean_inc(v_v_3775_);
lean_inc_ref(v_embeds_3768_);
v___x_3778_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3768_, v_v_3775_, v___x_3777_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v_bs_x27_3781_; size_t v___x_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = lean_unsigned_to_nat(0u);
v_bs_x27_3781_ = lean_array_uset(v_bs_3771_, v_i_3770_, v___x_3780_);
v___x_3782_ = ((size_t)1ULL);
v___x_3783_ = lean_usize_add(v_i_3770_, v___x_3782_);
v___x_3784_ = lean_array_uset(v_bs_x27_3781_, v_i_3770_, v_a_3779_);
v_i_3770_ = v___x_3783_;
v_bs_3771_ = v___x_3784_;
goto _start;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_bs_3771_);
lean_dec_ref(v_embeds_3768_);
v_a_3786_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3778_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3778_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(lean_object* v___x_3794_, lean_object* v_embeds_3795_, lean_object* v_indent_3796_, lean_object* v_x_3797_, lean_object* v_tt_3798_){
_start:
{
lean_object* v_fst_3800_; lean_object* v_snd_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3914_; 
v_fst_3800_ = lean_ctor_get(v_x_3797_, 0);
v_snd_3801_ = lean_ctor_get(v_x_3797_, 1);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_x_3797_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3803_ = v_x_3797_;
v_isShared_3804_ = v_isSharedCheck_3914_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_snd_3801_);
lean_inc(v_fst_3800_);
lean_dec(v_x_3797_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3914_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_array_get(v___x_3794_, v_embeds_3795_, v_fst_3800_);
lean_dec(v_fst_3800_);
switch(lean_obj_tag(v___x_3805_))
{
case 0:
{
lean_object* v_ctx_3806_; lean_object* v_infos_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3803_);
lean_dec(v_snd_3801_);
lean_dec(v_indent_3796_);
lean_dec_ref(v_embeds_3795_);
v_ctx_3806_ = lean_ctor_get(v___x_3805_, 0);
v_infos_3807_ = lean_ctor_get(v___x_3805_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3809_ = v___x_3805_;
v_isShared_3810_ = v_isSharedCheck_3818_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_infos_3807_);
lean_inc(v_ctx_3806_);
lean_dec(v___x_3805_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3818_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3811_ = l_Lean_Widget_tagCodeInfos(v_ctx_3806_, v_infos_3807_, v_tt_3798_);
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
v___x_3813_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 2);
lean_ctor_set(v___x_3809_, 1, v___x_3813_);
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
}
}
case 1:
{
lean_object* v_ctx_3819_; lean_object* v_lctx_3820_; lean_object* v_g_3821_; lean_object* v___f_3822_; lean_object* v___x_3823_; 
lean_del_object(v___x_3803_);
lean_dec(v_snd_3801_);
lean_dec_ref(v_tt_3798_);
lean_dec(v_indent_3796_);
lean_dec_ref(v_embeds_3795_);
v_ctx_3819_ = lean_ctor_get(v___x_3805_, 0);
lean_inc_ref(v_ctx_3819_);
v_lctx_3820_ = lean_ctor_get(v___x_3805_, 1);
lean_inc_ref(v_lctx_3820_);
v_g_3821_ = lean_ctor_get(v___x_3805_, 2);
lean_inc(v_g_3821_);
lean_dec_ref(v___x_3805_);
v___f_3822_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3822_, 0, v_g_3821_);
v___x_3823_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_3819_, v_lctx_3820_, v___f_3822_);
return v___x_3823_;
}
case 2:
{
lean_object* v_wi_3824_; lean_object* v_alt_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_tt_3798_);
lean_dec(v_indent_3796_);
v_wi_3824_ = lean_ctor_get(v___x_3805_, 0);
v_alt_3825_ = lean_ctor_get(v___x_3805_, 1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3827_ = v___x_3805_;
v_isShared_3828_ = v_isSharedCheck_3845_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_alt_3825_);
lean_inc(v_wi_3824_);
lean_dec(v___x_3805_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3845_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3795_, v_alt_3825_, v_snd_3801_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3844_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v_a_3830_);
v___x_3835_ = v___x_3827_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_wi_3824_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 2);
lean_ctor_set(v___x_3803_, 1, v___x_3836_);
lean_ctor_set(v___x_3803_, 0, v___x_3835_);
v___x_3838_ = v___x_3803_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3838_);
v___x_3840_ = v___x_3832_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
else
{
lean_del_object(v___x_3827_);
lean_dec_ref(v_wi_3824_);
lean_del_object(v___x_3803_);
return v___x_3829_;
}
}
}
case 3:
{
lean_object* v_cls_3846_; lean_object* v_msg_3847_; uint8_t v_collapsed_3848_; lean_object* v_children_3849_; lean_object* v_col_3850_; lean_object* v_children_3852_; 
lean_dec_ref(v_tt_3798_);
v_cls_3846_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_cls_3846_);
v_msg_3847_ = lean_ctor_get(v___x_3805_, 1);
lean_inc(v_msg_3847_);
v_collapsed_3848_ = lean_ctor_get_uint8(v___x_3805_, sizeof(void*)*3);
v_children_3849_ = lean_ctor_get(v___x_3805_, 2);
lean_inc_ref(v_children_3849_);
lean_dec_ref(v___x_3805_);
v_col_3850_ = lean_nat_add(v_indent_3796_, v_snd_3801_);
lean_dec(v_snd_3801_);
if (lean_obj_tag(v_children_3849_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3886_; 
v_a_3867_ = lean_ctor_get(v_children_3849_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_children_3849_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3869_ = v_children_3849_;
v_isShared_3870_ = v_isSharedCheck_3886_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v_children_3849_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3886_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
size_t v_sz_3871_; size_t v___x_3872_; lean_object* v___x_3873_; 
v_sz_3871_ = lean_array_size(v_a_3867_);
v___x_3872_ = ((size_t)0ULL);
lean_inc_ref(v_embeds_3795_);
v___x_3873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3850_, v_embeds_3795_, v_sz_3871_, v___x_3872_, v_a_3867_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3873_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v_a_3874_);
v___x_3876_ = v___x_3869_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
v_children_3852_ = v___x_3876_;
goto v___jp_3851_;
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3869_);
lean_dec(v_col_3850_);
lean_dec(v_msg_3847_);
lean_dec(v_cls_3846_);
lean_del_object(v___x_3803_);
lean_dec(v_indent_3796_);
lean_dec_ref(v_embeds_3795_);
v_a_3878_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3873_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3873_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3910_; 
v_a_3887_ = lean_ctor_get(v_children_3849_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_children_3849_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3889_ = v_children_3849_;
v_isShared_3890_ = v_isSharedCheck_3910_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v_children_3849_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3910_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
size_t v_sz_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
v_sz_3891_ = lean_array_size(v_a_3887_);
v___x_3892_ = ((size_t)0ULL);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__1(v_sz_3891_, v___x_3892_, v_a_3887_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref(v___x_3893_);
v___x_3895_ = lean_unsigned_to_nat(2u);
v___x_3896_ = lean_nat_add(v_col_3850_, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v_a_3894_);
v___x_3898_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_3897_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3898_);
v___x_3900_ = v___x_3889_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
v_children_3852_ = v___x_3900_;
goto v___jp_3851_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3889_);
lean_dec(v_col_3850_);
lean_dec(v_msg_3847_);
lean_dec(v_cls_3846_);
lean_del_object(v___x_3803_);
lean_dec(v_indent_3796_);
lean_dec_ref(v_embeds_3795_);
v_a_3902_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3893_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3893_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
v___jp_3851_:
{
lean_object* v___x_3853_; 
v___x_3853_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3795_, v_msg_3847_, v_col_3850_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3866_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3866_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3866_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3858_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_3858_, 0, v_indent_3796_);
lean_ctor_set(v___x_3858_, 1, v_cls_3846_);
lean_ctor_set(v___x_3858_, 2, v_a_3854_);
lean_ctor_set(v___x_3858_, 3, v_children_3852_);
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*4, v_collapsed_3848_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0, &l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0_once, _init_l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__0___closed__0);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 2);
lean_ctor_set(v___x_3803_, 1, v___x_3859_);
lean_ctor_set(v___x_3803_, 0, v___x_3858_);
v___x_3861_ = v___x_3803_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v___x_3861_);
v___x_3863_ = v___x_3856_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_dec_ref(v_children_3852_);
lean_dec(v_cls_3846_);
lean_del_object(v___x_3803_);
lean_dec(v_indent_3796_);
return v___x_3853_;
}
}
}
default: 
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_del_object(v___x_3803_);
lean_dec(v_snd_3801_);
lean_dec(v_indent_3796_);
lean_dec_ref(v_embeds_3795_);
v___x_3911_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3798_);
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed(lean_object* v___x_3915_, lean_object* v_embeds_3916_, lean_object* v_indent_3917_, lean_object* v_x_3918_, lean_object* v_tt_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1(v___x_3915_, v_embeds_3916_, v_indent_3917_, v_x_3918_, v_tt_3919_);
lean_dec(v___x_3915_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(lean_object* v_embeds_3922_, lean_object* v_fmt_3923_, lean_object* v_indent_3924_){
_start:
{
lean_object* v___x_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3926_ = l_Lean_Widget_instInhabitedEmbedFmt_default;
lean_inc(v_indent_3924_);
v___f_3927_ = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3927_, 0, v___x_3926_);
lean_closure_set(v___f_3927_, 1, v_embeds_3922_);
lean_closure_set(v___f_3927_, 2, v_indent_3924_);
v___x_3928_ = l_Std_Format_defWidth;
v___x_3929_ = l_Lean_Widget_TaggedText_prettyTagged(v_fmt_3923_, v_indent_3924_, v___x_3928_);
v___x_3930_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v___f_3927_, v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT___boxed(lean_object* v_embeds_3931_, lean_object* v_fmt_3932_, lean_object* v_indent_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_embeds_3931_, v_fmt_3932_, v_indent_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0___boxed(lean_object* v_col_3936_, lean_object* v_embeds_3937_, lean_object* v_sz_3938_, lean_object* v_i_3939_, lean_object* v_bs_3940_, lean_object* v___y_3941_){
_start:
{
size_t v_sz_boxed_3942_; size_t v_i_boxed_3943_; lean_object* v_res_3944_; 
v_sz_boxed_3942_ = lean_unbox_usize(v_sz_3938_);
lean_dec(v_sz_3938_);
v_i_boxed_3943_ = lean_unbox_usize(v_i_3939_);
lean_dec(v_i_3939_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__0(v_col_3936_, v_embeds_3937_, v_sz_boxed_3942_, v_i_boxed_3943_, v_bs_3940_);
lean_dec(v_col_3936_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(lean_object* v_00_u03b1_3945_, lean_object* v_00_u03b2_3946_, lean_object* v_f_3947_, lean_object* v_x_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___redArg(v_f_3947_, v_x_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2___boxed(lean_object* v_00_u03b1_3951_, lean_object* v_00_u03b2_3952_, lean_object* v_f_3953_, lean_object* v_x_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2(v_00_u03b1_3951_, v_00_u03b2_3952_, v_f_3953_, v_x_3954_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(lean_object* v_00_u03b1_3957_, lean_object* v_00_u03b2_3958_, lean_object* v_f_3959_, size_t v_sz_3960_, size_t v_i_3961_, lean_object* v_bs_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___redArg(v_f_3959_, v_sz_3960_, v_i_3961_, v_bs_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3965_, lean_object* v_00_u03b2_3966_, lean_object* v_f_3967_, lean_object* v_sz_3968_, lean_object* v_i_3969_, lean_object* v_bs_3970_, lean_object* v___y_3971_){
_start:
{
size_t v_sz_boxed_3972_; size_t v_i_boxed_3973_; lean_object* v_res_3974_; 
v_sz_boxed_3972_ = lean_unbox_usize(v_sz_3968_);
lean_dec(v_sz_3968_);
v_i_boxed_3973_ = lean_unbox_usize(v_i_3969_);
lean_dec(v_i_3969_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT_spec__2_spec__2(v_00_u03b1_3965_, v_00_u03b2_3966_, v_f_3967_, v_sz_boxed_3972_, v_i_boxed_3973_, v_bs_3970_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0(lean_object* v_x_3975_, lean_object* v_tt_3976_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___lam__0___boxed(lean_object* v_x_3979_, lean_object* v_tt_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Widget_msgToInteractive___lam__0(v_x_3979_, v_tt_3980_);
lean_dec_ref(v_x_3979_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive(lean_object* v_msgData_3983_, uint8_t v_hasWidgets_3984_, lean_object* v_indent_3985_){
_start:
{
if (v_hasWidgets_3984_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___f_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_indent_3985_);
v___x_3987_ = lean_box(0);
v___x_3988_ = l_Lean_MessageData_format(v_msgData_3983_, v___x_3987_);
v___f_3989_ = ((lean_object*)(l_Lean_Widget_msgToInteractive___closed__0));
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = l_Std_Format_defWidth;
v___x_3992_ = l_Lean_Widget_TaggedText_prettyTagged(v___x_3988_, v___x_3990_, v___x_3991_);
v___x_3993_ = l_Lean_Widget_TaggedText_rewrite___redArg(v___f_3989_, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v___x_3995_; 
v___x_3995_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractiveAux(v_msgData_3983_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v_fst_3997_; lean_object* v_snd_3998_; lean_object* v___x_3999_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref(v___x_3995_);
v_fst_3997_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_fst_3997_);
v_snd_3998_ = lean_ctor_get(v_a_3996_, 1);
lean_inc(v_snd_3998_);
lean_dec(v_a_3996_);
v___x_3999_ = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_msgToInteractive_fmtToTT(v_snd_3998_, v_fst_3997_, v_indent_3985_);
return v___x_3999_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_indent_3985_);
v_a_4000_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3995_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3995_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractive___boxed(lean_object* v_msgData_4008_, lean_object* v_hasWidgets_4009_, lean_object* v_indent_4010_, lean_object* v_a_4011_){
_start:
{
uint8_t v_hasWidgets_boxed_4012_; lean_object* v_res_4013_; 
v_hasWidgets_boxed_4012_ = lean_unbox(v_hasWidgets_4009_);
v_res_4013_ = l_Lean_Widget_msgToInteractive(v_msgData_4008_, v_hasWidgets_boxed_4012_, v_indent_4010_);
return v_res_4013_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(lean_object* v_x_4017_){
_start:
{
lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4018_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___closed__1));
v___x_4019_ = lean_name_eq(v_x_4017_, v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__0___boxed(lean_object* v_x_4020_){
_start:
{
uint8_t v_res_4021_; lean_object* v_r_4022_; 
v_res_4021_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__0(v_x_4020_);
lean_dec(v_x_4020_);
v_r_4022_ = lean_box(v_res_4021_);
return v_r_4022_;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(lean_object* v_x_4028_){
_start:
{
lean_object* v___x_4029_; uint8_t v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___closed__2));
v___x_4030_ = lean_name_eq(v_x_4028_, v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___lam__1___boxed(lean_object* v_x_4031_){
_start:
{
uint8_t v_res_4032_; lean_object* v_r_4033_; 
v_res_4032_ = l_Lean_Widget_msgToInteractiveDiagnostic___lam__1(v_x_4031_);
lean_dec(v_x_4031_);
v_r_4033_ = lean_box(v_res_4032_);
return v_r_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object* v_text_4072_, lean_object* v_m_4073_, uint8_t v_hasWidgets_4074_){
_start:
{
lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v_pos_4089_; lean_object* v_endPos_4090_; uint8_t v_keepFullRange_4091_; uint8_t v_severity_4092_; uint8_t v_isSilent_4093_; lean_object* v_data_4094_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4119_; uint8_t v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___f_4143_; lean_object* v___f_4144_; lean_object* v___y_4146_; lean_object* v___y_4147_; uint8_t v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4159_; uint8_t v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v_low_4179_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4193_; 
v_pos_4089_ = lean_ctor_get(v_m_4073_, 1);
lean_inc_ref_n(v_pos_4089_, 2);
v_endPos_4090_ = lean_ctor_get(v_m_4073_, 2);
lean_inc(v_endPos_4090_);
v_keepFullRange_4091_ = lean_ctor_get_uint8(v_m_4073_, sizeof(void*)*5);
v_severity_4092_ = lean_ctor_get_uint8(v_m_4073_, sizeof(void*)*5 + 1);
v_isSilent_4093_ = lean_ctor_get_uint8(v_m_4073_, sizeof(void*)*5 + 2);
v_data_4094_ = lean_ctor_get(v_m_4073_, 4);
lean_inc(v_data_4094_);
lean_dec_ref(v_m_4073_);
v___f_4143_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__2));
v___f_4144_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__3));
lean_inc_ref(v_text_4072_);
v_low_4179_ = l_Lean_FileMap_leanPosToLspPos(v_text_4072_, v_pos_4089_);
if (lean_obj_tag(v_endPos_4090_) == 0)
{
lean_inc_ref(v_pos_4089_);
v___y_4193_ = v_pos_4089_;
goto v___jp_4192_;
}
else
{
lean_object* v_val_4213_; 
v_val_4213_ = lean_ctor_get(v_endPos_4090_, 0);
lean_inc(v_val_4213_);
v___y_4193_ = v_val_4213_;
goto v___jp_4192_;
}
v___jp_4076_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___y_4077_);
v___x_4087_ = lean_box(0);
lean_inc(v___y_4079_);
lean_inc(v___y_4081_);
lean_inc(v___y_4083_);
lean_inc(v___y_4084_);
v___x_4088_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4088_, 0, v___y_4078_);
lean_ctor_set(v___x_4088_, 1, v___x_4086_);
lean_ctor_set(v___x_4088_, 2, v___y_4082_);
lean_ctor_set(v___x_4088_, 3, v___y_4084_);
lean_ctor_set(v___x_4088_, 4, v___y_4085_);
lean_ctor_set(v___x_4088_, 5, v___y_4083_);
lean_ctor_set(v___x_4088_, 6, v___y_4080_);
lean_ctor_set(v___x_4088_, 7, v___y_4081_);
lean_ctor_set(v___x_4088_, 8, v___y_4079_);
lean_ctor_set(v___x_4088_, 9, v___x_4087_);
lean_ctor_set(v___x_4088_, 10, v___x_4087_);
return v___x_4088_;
}
v___jp_4095_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = l_Lean_MessageData_kind(v_data_4094_);
lean_dec(v_data_4094_);
v___x_4106_ = l_Lean_errorNameOfKind_x3f(v___x_4105_);
lean_dec(v___x_4105_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_box(0);
v___y_4077_ = v___y_4096_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___y_4099_;
v___y_4080_ = v___y_4104_;
v___y_4081_ = v___y_4100_;
v___y_4082_ = v___y_4101_;
v___y_4083_ = v___y_4102_;
v___y_4084_ = v___y_4103_;
v___y_4085_ = v___x_4107_;
goto v___jp_4076_;
}
else
{
lean_object* v_val_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4117_; 
v_val_4108_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4110_ = v___x_4106_;
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_val_4108_);
lean_dec(v___x_4106_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4112_ = l_Lean_Name_toString(v_val_4108_, v___y_4097_);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4113_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
v___y_4077_ = v___y_4096_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___y_4099_;
v___y_4080_ = v___y_4104_;
v___y_4081_ = v___y_4100_;
v___y_4082_ = v___y_4101_;
v___y_4083_ = v___y_4102_;
v___y_4084_ = v___y_4103_;
v___y_4085_ = v___x_4115_;
goto v___jp_4076_;
}
}
}
}
v___jp_4118_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_unsigned_to_nat(0u);
lean_inc(v_data_4094_);
v___x_4128_ = l_Lean_Widget_msgToInteractive(v_data_4094_, v_hasWidgets_4074_, v___x_4127_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref(v___x_4128_);
v___y_4096_ = v___y_4119_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___y_4121_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4122_;
v___y_4101_ = v___y_4123_;
v___y_4102_ = v___y_4124_;
v___y_4103_ = v___y_4125_;
v___y_4104_ = v_a_4129_;
goto v___jp_4095_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4142_; 
v_a_4130_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4132_ = v___x_4128_;
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4128_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4134_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__0));
v___x_4135_ = lean_io_error_to_string(v_a_4130_);
v___x_4136_ = lean_string_append(v___x_4134_, v___x_4135_);
lean_dec_ref(v___x_4135_);
v___x_4137_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__1));
v___x_4138_ = lean_string_append(v___x_4136_, v___x_4137_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4138_);
v___x_4140_ = v___x_4132_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
v___y_4096_ = v___y_4119_;
v___y_4097_ = v___y_4120_;
v___y_4098_ = v___y_4121_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4122_;
v___y_4101_ = v___y_4123_;
v___y_4102_ = v___y_4124_;
v___y_4103_ = v___y_4125_;
v___y_4104_ = v___x_4140_;
goto v___jp_4095_;
}
}
}
}
v___jp_4145_:
{
uint8_t v___x_4153_; 
lean_inc(v_data_4094_);
v___x_4153_ = l_Lean_MessageData_hasTag(v___f_4144_, v_data_4094_);
if (v___x_4153_ == 0)
{
uint8_t v___x_4154_; 
lean_inc(v_data_4094_);
v___x_4154_ = l_Lean_MessageData_hasTag(v___f_4143_, v_data_4094_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_box(0);
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4147_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4149_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___x_4155_;
goto v___jp_4118_;
}
else
{
lean_object* v___x_4156_; 
v___x_4156_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__5));
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4147_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4149_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___x_4156_;
goto v___jp_4118_;
}
}
else
{
lean_object* v___x_4157_; 
v___x_4157_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__7));
v___y_4119_ = v___y_4146_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4147_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4149_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___x_4157_;
goto v___jp_4118_;
}
}
v___jp_4158_:
{
lean_object* v_source_x3f_4164_; uint8_t v___x_4165_; 
v_source_x3f_4164_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__9));
lean_inc(v_data_4094_);
v___x_4165_ = l_Lean_MessageData_isDeprecationWarning(v_data_4094_);
if (v___x_4165_ == 0)
{
uint8_t v___x_4166_; 
lean_inc(v_data_4094_);
v___x_4166_ = l_Lean_MessageData_isUnusedVariableWarning(v_data_4094_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_box(0);
v___y_4146_ = v___y_4159_;
v___y_4147_ = v___y_4161_;
v___y_4148_ = v___y_4160_;
v___y_4149_ = v___y_4162_;
v___y_4150_ = v_source_x3f_4164_;
v___y_4151_ = v___y_4163_;
v___y_4152_ = v___x_4167_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4168_; 
v___x_4168_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__11));
v___y_4146_ = v___y_4159_;
v___y_4147_ = v___y_4161_;
v___y_4148_ = v___y_4160_;
v___y_4149_ = v___y_4162_;
v___y_4150_ = v_source_x3f_4164_;
v___y_4151_ = v___y_4163_;
v___y_4152_ = v___x_4168_;
goto v___jp_4145_;
}
}
else
{
lean_object* v___x_4169_; 
v___x_4169_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__13));
v___y_4146_ = v___y_4159_;
v___y_4147_ = v___y_4161_;
v___y_4148_ = v___y_4160_;
v___y_4149_ = v___y_4162_;
v___y_4150_ = v_source_x3f_4164_;
v___y_4151_ = v___y_4163_;
v___y_4152_ = v___x_4169_;
goto v___jp_4145_;
}
}
v___jp_4170_:
{
lean_object* v___x_4174_; lean_object* v_severity_x3f_4175_; uint8_t v___x_4176_; 
v___x_4174_ = lean_box(v___y_4173_);
v_severity_x3f_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_severity_x3f_4175_, 0, v___x_4174_);
v___x_4176_ = 1;
if (v_isSilent_4093_ == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = lean_box(0);
v___y_4159_ = v___y_4171_;
v___y_4160_ = v___x_4176_;
v___y_4161_ = v___y_4172_;
v___y_4162_ = v_severity_x3f_4175_;
v___y_4163_ = v___x_4177_;
goto v___jp_4158_;
}
else
{
lean_object* v___x_4178_; 
v___x_4178_ = ((lean_object*)(l_Lean_Widget_msgToInteractiveDiagnostic___closed__14));
v___y_4159_ = v___y_4171_;
v___y_4160_ = v___x_4176_;
v___y_4161_ = v___y_4172_;
v___y_4162_ = v_severity_x3f_4175_;
v___y_4163_ = v___x_4178_;
goto v___jp_4158_;
}
}
v___jp_4180_:
{
lean_object* v_range_4183_; lean_object* v_fullRange_4184_; 
lean_inc_ref(v_low_4179_);
v_range_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_range_4183_, 0, v_low_4179_);
lean_ctor_set(v_range_4183_, 1, v___y_4182_);
v_fullRange_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_fullRange_4184_, 0, v_low_4179_);
lean_ctor_set(v_fullRange_4184_, 1, v___y_4181_);
switch(v_severity_4092_)
{
case 0:
{
uint8_t v___x_4185_; 
v___x_4185_ = 2;
v___y_4171_ = v_fullRange_4184_;
v___y_4172_ = v_range_4183_;
v___y_4173_ = v___x_4185_;
goto v___jp_4170_;
}
case 1:
{
uint8_t v___x_4186_; 
v___x_4186_ = 1;
v___y_4171_ = v_fullRange_4184_;
v___y_4172_ = v_range_4183_;
v___y_4173_ = v___x_4186_;
goto v___jp_4170_;
}
default: 
{
uint8_t v___x_4187_; 
v___x_4187_ = 0;
v___y_4171_ = v_fullRange_4184_;
v___y_4172_ = v_range_4183_;
v___y_4173_ = v___x_4187_;
goto v___jp_4170_;
}
}
}
v___jp_4188_:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_FileMap_leanPosToLspPos(v_text_4072_, v___y_4190_);
v___y_4181_ = v___y_4189_;
v___y_4182_ = v___x_4191_;
goto v___jp_4180_;
}
v___jp_4192_:
{
lean_object* v_fullHigh_4194_; 
lean_inc_ref(v_text_4072_);
v_fullHigh_4194_ = l_Lean_FileMap_leanPosToLspPos(v_text_4072_, v___y_4193_);
if (lean_obj_tag(v_endPos_4090_) == 0)
{
lean_dec_ref(v_pos_4089_);
lean_dec_ref(v_text_4072_);
lean_inc_ref(v_low_4179_);
v___y_4181_ = v_fullHigh_4194_;
v___y_4182_ = v_low_4179_;
goto v___jp_4180_;
}
else
{
if (v_keepFullRange_4091_ == 0)
{
lean_object* v_val_4195_; lean_object* v_line_4196_; lean_object* v_line_4197_; uint8_t v___x_4198_; 
v_val_4195_ = lean_ctor_get(v_endPos_4090_, 0);
lean_inc(v_val_4195_);
lean_dec_ref(v_endPos_4090_);
v_line_4196_ = lean_ctor_get(v_pos_4089_, 0);
lean_inc(v_line_4196_);
lean_dec_ref(v_pos_4089_);
v_line_4197_ = lean_ctor_get(v_val_4195_, 0);
v___x_4198_ = lean_nat_dec_lt(v_line_4196_, v_line_4197_);
if (v___x_4198_ == 0)
{
lean_dec(v_line_4196_);
v___y_4189_ = v_fullHigh_4194_;
v___y_4190_ = v_val_4195_;
goto v___jp_4188_;
}
else
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4209_; 
v_isSharedCheck_4209_ = !lean_is_exclusive(v_val_4195_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; lean_object* v_unused_4211_; 
v_unused_4210_ = lean_ctor_get(v_val_4195_, 1);
lean_dec(v_unused_4210_);
v_unused_4211_ = lean_ctor_get(v_val_4195_, 0);
lean_dec(v_unused_4211_);
v___x_4200_ = v_val_4195_;
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v_val_4195_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4202_ = lean_unsigned_to_nat(1u);
v___x_4203_ = lean_nat_add(v_line_4196_, v___x_4202_);
lean_dec(v_line_4196_);
v___x_4204_ = lean_unsigned_to_nat(0u);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4204_);
lean_ctor_set(v___x_4200_, 0, v___x_4203_);
v___x_4206_ = v___x_4200_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4203_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4204_);
v___x_4206_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_FileMap_leanPosToLspPos(v_text_4072_, v___x_4206_);
v___y_4181_ = v_fullHigh_4194_;
v___y_4182_ = v___x_4207_;
goto v___jp_4180_;
}
}
}
}
else
{
lean_object* v_val_4212_; 
lean_dec_ref(v_pos_4089_);
v_val_4212_ = lean_ctor_get(v_endPos_4090_, 0);
lean_inc(v_val_4212_);
lean_dec_ref(v_endPos_4090_);
v___y_4189_ = v_fullHigh_4194_;
v___y_4190_ = v_val_4212_;
goto v___jp_4188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_msgToInteractiveDiagnostic___boxed(lean_object* v_text_4214_, lean_object* v_m_4215_, lean_object* v_hasWidgets_4216_, lean_object* v_a_4217_){
_start:
{
uint8_t v_hasWidgets_boxed_4218_; lean_object* v_res_4219_; 
v_hasWidgets_boxed_4218_ = lean_unbox(v_hasWidgets_4216_);
v_res_4219_ = l_Lean_Widget_msgToInteractiveDiagnostic(v_text_4214_, v_m_4215_, v_hasWidgets_boxed_4218_);
return v_res_4219_;
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
