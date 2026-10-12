// Lean compiler output
// Module: Lean.Meta.CongrTheorems
// Imports: public import Lean.AddDecl public import Lean.ReservedNameAction import Lean.Structure import Lean.Meta.Tactic.Subst import Lean.Meta.FunInfo
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCongrArgKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCongrArgKind;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.CongrArgKind.fixed"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.CongrArgKind.fixedNoParam"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.CongrArgKind.eq"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.CongrArgKind.cast"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__7 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.CongrArgKind.heq"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__8 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__9 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.CongrArgKind.subsingletonInst"};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__10 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__11 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind_repr___closed__11_value;
static lean_once_cell_t l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__12;
static lean_once_cell_t l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCongrArgKind_repr___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCongrArgKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCongrArgKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCongrArgKind___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCongrArgKind = (const lean_object*)&l_Lean_Meta_instReprCongrArgKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqCongrArgKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqCongrArgKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqCongrArgKind___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqCongrArgKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqCongrArgKind = (const lean_object*)&l_Lean_Meta_instBEqCongrArgKind___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "failed to generate `hcongr` theorem: expected "};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " arguments, but got "};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " for"};
static const lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_getCongrSimpKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_getCongrSimpKinds___closed__0 = (const lean_object*)&l_Lean_Meta_getCongrSimpKinds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 85, 152, 16, 239, 41, 62, 212)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mkProof.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.CongrTheorems"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.CongrTheorems.0.Lean.Meta.mkCongrSimpCore\?.mk\?.go"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "e_"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_hcongrThmSuffixBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hcongr"};
static const lean_object* l_Lean_Meta_hcongrThmSuffixBase___closed__0 = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_hcongrThmSuffixBase = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBase___closed__0_value;
static const lean_string_object l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hcongr_"};
static const lean_object* l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0 = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_hcongrThmSuffixBasePrefix = (const lean_object*)&l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_congrSimpSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "congr_simp"};
static const lean_object* l_Lean_Meta_congrSimpSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_congrSimpSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_congrSimpSuffix = (const lean_object*)&l_Lean_Meta_congrSimpSuffix___closed__0_value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 141, 208, 58, 7, 230, 107, 112)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CongrTheorems"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 224, 213, 6, 189, 51, 239, 200)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 140, 44, 156, 105, 54, 226, 29)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 41, 252, 212, 29, 253, 12, 67)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 81, 65, 75, 45, 89, 43, 189)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 167, 132, 254, 103, 165, 136, 43)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 26, 60, 185, 66, 206, 188, 95)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 26, 15, 119, 133, 253, 114, 42)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 116, 182, 41, 116, 135, 13, 170)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 27, 116, 143, 64, 80, 226, 54)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "congrKindsExt"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 7, 195, 199, 246, 152, 65, 143)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrKindsExt;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declared `"};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.mkHCongrWithArityForConst\?"};
static const lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.mkCongrSimpForConst\?"};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to generate `"};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1;
static const lean_string_object l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Meta_CongrArgKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_CongrArgKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_CongrArgKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Meta_CongrArgKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Meta_CongrArgKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg(lean_object* v_fixed_24_){
_start:
{
lean_inc(v_fixed_24_);
return v_fixed_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___redArg___boxed(lean_object* v_fixed_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_CongrArgKind_fixed_elim___redArg(v_fixed_25_);
lean_dec(v_fixed_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_fixed_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_fixed_30_){
_start:
{
lean_inc(v_fixed_30_);
return v_fixed_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_fixed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_fixed_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_CongrArgKind_fixed_elim(lean_box(0), v_t_28_, lean_box(0), v_fixed_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixed_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_fixed_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_CongrArgKind_fixed_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_fixed_35_);
lean_dec(v_fixed_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(lean_object* v_fixedNoParam_38_){
_start:
{
lean_inc(v_fixedNoParam_38_);
return v_fixedNoParam_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg___boxed(lean_object* v_fixedNoParam_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim___redArg(v_fixedNoParam_39_);
lean_dec(v_fixedNoParam_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_fixedNoParam_44_){
_start:
{
lean_inc(v_fixedNoParam_44_);
return v_fixedNoParam_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_fixedNoParam_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_fixedNoParam_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(lean_box(0), v_t_42_, lean_box(0), v_fixedNoParam_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_fixedNoParam_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_fixedNoParam_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_CongrArgKind_fixedNoParam_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_fixedNoParam_49_);
lean_dec(v_fixedNoParam_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg(lean_object* v_eq_52_){
_start:
{
lean_inc(v_eq_52_);
return v_eq_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___redArg___boxed(lean_object* v_eq_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_CongrArgKind_eq_elim___redArg(v_eq_53_);
lean_dec(v_eq_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_eq_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_eq_58_){
_start:
{
lean_inc(v_eq_58_);
return v_eq_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_eq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_eq_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_CongrArgKind_eq_elim(lean_box(0), v_t_56_, lean_box(0), v_eq_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_eq_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_eq_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Meta_CongrArgKind_eq_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_eq_63_);
lean_dec(v_eq_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg(lean_object* v_cast_66_){
_start:
{
lean_inc(v_cast_66_);
return v_cast_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___redArg___boxed(lean_object* v_cast_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_CongrArgKind_cast_elim___redArg(v_cast_67_);
lean_dec(v_cast_67_);
return v_res_68_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_cast_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_cast_72_){
_start:
{
lean_inc(v_cast_72_);
return v_cast_72_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_cast_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_cast_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_CongrArgKind_cast_elim(lean_box(0), v_t_70_, lean_box(0), v_cast_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_cast_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_cast_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Lean_Meta_CongrArgKind_cast_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_cast_77_);
lean_dec(v_cast_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg(lean_object* v_heq_80_){
_start:
{
lean_inc(v_heq_80_);
return v_heq_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___redArg___boxed(lean_object* v_heq_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_CongrArgKind_heq_elim___redArg(v_heq_81_);
lean_dec(v_heq_81_);
return v_res_82_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_heq_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_heq_86_){
_start:
{
lean_inc(v_heq_86_);
return v_heq_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_heq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_heq_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_CongrArgKind_heq_elim(lean_box(0), v_t_84_, lean_box(0), v_heq_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_heq_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_heq_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l_Lean_Meta_CongrArgKind_heq_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_heq_91_);
lean_dec(v_heq_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(lean_object* v_subsingletonInst_94_){
_start:
{
lean_inc(v_subsingletonInst_94_);
return v_subsingletonInst_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg___boxed(lean_object* v_subsingletonInst_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim___redArg(v_subsingletonInst_95_);
lean_dec(v_subsingletonInst_95_);
return v_res_96_;
}
}
lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_object* v_motive_97_, uint8_t v_t_98_, lean_object* v_h_99_, lean_object* v_subsingletonInst_100_){
_start:
{
lean_inc(v_subsingletonInst_100_);
return v_subsingletonInst_100_;
}
}
LEAN_EXPORT void l_Lean_Meta_CongrArgKind_subsingletonInst_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_98_ = stack[1].m_num;
lean_object* v_subsingletonInst_100_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(lean_box(0), v_t_98_, lean_box(0), v_subsingletonInst_100_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_CongrArgKind_subsingletonInst_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_subsingletonInst_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Lean_Meta_CongrArgKind_subsingletonInst_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_subsingletonInst_105_);
lean_dec(v_subsingletonInst_105_);
return v_res_107_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind_default(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCongrArgKind(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
lean_object* l_Lean_Meta_instReprCongrArgKind_repr(uint8_t v_x_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_142_; lean_object* v___y_149_; lean_object* v___y_156_; lean_object* v___y_163_; lean_object* v___y_170_; 
switch(v_x_132_)
{
case 0:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_133_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_135_ = v___x_178_;
goto v___jp_134_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_135_ = v___x_179_;
goto v___jp_134_;
}
}
case 1:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_133_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_142_ = v___x_182_;
goto v___jp_141_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_142_ = v___x_183_;
goto v___jp_141_;
}
}
case 2:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_133_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_149_ = v___x_186_;
goto v___jp_148_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_149_ = v___x_187_;
goto v___jp_148_;
}
}
case 3:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_133_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_156_ = v___x_190_;
goto v___jp_155_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_156_ = v___x_191_;
goto v___jp_155_;
}
}
case 4:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_133_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_163_ = v___x_194_;
goto v___jp_162_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_163_ = v___x_195_;
goto v___jp_162_;
}
}
default: 
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1024u);
v___x_197_ = lean_nat_dec_le(v___x_196_, v_prec_133_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__12, &l_Lean_Meta_instReprCongrArgKind_repr___closed__12_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__12);
v___y_170_ = v___x_198_;
goto v___jp_169_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_instReprCongrArgKind_repr___closed__13, &l_Lean_Meta_instReprCongrArgKind_repr___closed__13_once, _init_l_Lean_Meta_instReprCongrArgKind_repr___closed__13);
v___y_170_ = v___x_199_;
goto v___jp_169_;
}
}
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__1));
lean_inc(v___y_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_133_);
return v___x_140_;
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__3));
lean_inc(v___y_142_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_133_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__5));
lean_inc(v___y_149_);
v___x_151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_151_, 0, v___y_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_152_);
v___x_154_ = l_Repr_addAppParen(v___x_153_, v_prec_133_);
return v___x_154_;
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__7));
lean_inc(v___y_156_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_prec_133_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__9));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_133_);
return v___x_168_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_instReprCongrArgKind_repr___closed__11));
lean_inc(v___y_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_173_);
v___x_175_ = l_Repr_addAppParen(v___x_174_, v_prec_133_);
return v___x_175_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_instReprCongrArgKind_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_132_ = stack[0].m_num;
lean_object* v_prec_133_ = stack[1].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_132_, v_prec_133_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCongrArgKind_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
uint8_t v_x_333__boxed_203_; lean_object* v_res_204_; 
v_x_333__boxed_203_ = lean_unbox(v_x_201_);
v_res_204_ = l_Lean_Meta_instReprCongrArgKind_repr(v_x_333__boxed_203_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_204_;
}
}
uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t v_x_207_, uint8_t v_y_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_209_ = lean_box(v_x_207_);
v___x_210_ = lean_obj_tag_nat(v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = lean_box(v_y_208_);
v___x_212_ = lean_obj_tag_nat(v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_nat_dec_eq(v___x_210_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Lean_Meta_instBEqCongrArgKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_207_ = stack[0].m_num;
uint8_t v_y_208_ = stack[1].m_num;
uint8_t v_res_214_;
v_res_214_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_207_, v_y_208_);
stack->m_num = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqCongrArgKind_beq___boxed(lean_object* v_x_215_, lean_object* v_y_216_){
_start:
{
uint8_t v_x_24__boxed_217_; uint8_t v_y_25__boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_x_24__boxed_217_ = lean_unbox(v_x_215_);
v_y_25__boxed_218_ = lean_unbox(v_y_216_);
v_res_219_ = l_Lean_Meta_instBEqCongrArgKind_beq(v_x_24__boxed_217_, v_y_25__boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(lean_object* v_as_224_, size_t v_sz_225_, size_t v_i_226_, lean_object* v_b_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_226_, v_sz_225_);
if (v___x_228_ == 0)
{
return v_b_227_;
}
else
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v_a_229_ = lean_array_uget_borrowed(v_as_224_, v_i_226_);
lean_inc_ref(v_b_227_);
v___x_230_ = l_Lean_LocalContext_getFVar_x21(v_b_227_, v_a_229_);
v___x_231_ = l_Lean_LocalDecl_fvarId(v___x_230_);
v___x_232_ = l_Lean_LocalDecl_userName(v___x_230_);
lean_dec_ref(v___x_230_);
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___closed__0));
v___x_234_ = lean_name_append_after(v___x_232_, v___x_233_);
v___x_235_ = l_Lean_LocalContext_setUserName(v_b_227_, v___x_231_, v___x_234_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_226_, v___x_236_);
v_i_226_ = v___x_237_;
v_b_227_ = v___x_235_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_224_ = stack[0].m_obj;
size_t v_sz_225_ = stack[1].m_num;
size_t v_i_226_ = stack[2].m_num;
lean_object* v_b_227_ = stack[3].m_obj;
lean_object* v_res_239_;
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_224_, v_sz_225_, v_i_226_, v_b_227_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0___boxed(lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_as_240_, v_sz_boxed_244_, v_i_boxed_245_, v_b_243_);
lean_dec_ref(v_as_240_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(lean_object* v_ys_247_, lean_object* v_lctx_248_){
_start:
{
size_t v_sz_249_; size_t v___x_250_; lean_object* v___x_251_; 
v_sz_249_ = lean_array_size(v_ys_247_);
v___x_250_ = ((size_t)0ULL);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames_spec__0(v_ys_247_, v_sz_249_, v___x_250_, v_lctx_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames___boxed(lean_object* v_ys_252_, lean_object* v_lctx_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_252_, v_lctx_253_);
lean_dec_ref(v_ys_252_);
return v_res_254_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(lean_object* v_as_255_, size_t v_sz_256_, size_t v_i_257_, lean_object* v_b_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_lt(v_i_257_, v_sz_256_);
if (v___x_259_ == 0)
{
return v_b_258_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; 
v_a_260_ = lean_array_uget_borrowed(v_as_255_, v_i_257_);
lean_inc_ref(v_b_258_);
v___x_261_ = l_Lean_LocalContext_getFVar_x21(v_b_258_, v_a_260_);
v___x_262_ = l_Lean_LocalDecl_fvarId(v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = 0;
v___x_264_ = l_Lean_LocalContext_setBinderInfo(v_b_258_, v___x_262_, v___x_263_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_257_, v___x_265_);
v_i_257_ = v___x_266_;
v_b_258_ = v___x_264_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_255_ = stack[0].m_obj;
size_t v_sz_256_ = stack[1].m_num;
size_t v_i_257_ = stack[2].m_num;
lean_object* v_b_258_ = stack[3].m_obj;
lean_object* v_res_268_;
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_255_, v_sz_256_, v_i_257_, v_b_258_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0___boxed(lean_object* v_as_269_, lean_object* v_sz_270_, lean_object* v_i_271_, lean_object* v_b_272_){
_start:
{
size_t v_sz_boxed_273_; size_t v_i_boxed_274_; lean_object* v_res_275_; 
v_sz_boxed_273_ = lean_unbox_usize(v_sz_270_);
lean_dec(v_sz_270_);
v_i_boxed_274_ = lean_unbox_usize(v_i_271_);
lean_dec(v_i_271_);
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_as_269_, v_sz_boxed_273_, v_i_boxed_274_, v_b_272_);
lean_dec_ref(v_as_269_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(lean_object* v_ys_276_, lean_object* v_lctx_277_){
_start:
{
size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; 
v_sz_278_ = lean_array_size(v_ys_276_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD_spec__0(v_ys_276_, v_sz_278_, v___x_279_, v_lctx_277_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD___boxed(lean_object* v_ys_281_, lean_object* v_lctx_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_281_, v_lctx_282_);
lean_dec_ref(v_ys_281_);
return v_res_283_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_284_, lean_object* v_b_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
v___x_291_ = lean_apply_6(v_k_284_, v_b_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, lean_box(0));
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_284_ = stack[0].m_obj;
lean_object* v_b_285_ = stack[1].m_obj;
lean_object* v___y_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_284_, v_b_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_293_, lean_object* v_b_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_293_, v_b_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_301_, uint8_t v_bi_302_, lean_object* v_type_303_, lean_object* v_k_304_, uint8_t v_kind_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; 
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_311_, 0, v_k_304_);
v___x_312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_301_, v_bi_302_, v_type_303_, v___f_311_, v_kind_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_312_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_312_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_301_ = stack[0].m_obj;
uint8_t v_bi_302_ = stack[1].m_num;
lean_object* v_type_303_ = stack[2].m_obj;
lean_object* v_k_304_ = stack[3].m_obj;
uint8_t v_kind_305_ = stack[4].m_num;
lean_object* v___y_306_ = stack[5].m_obj;
lean_object* v___y_307_ = stack[6].m_obj;
lean_object* v___y_308_ = stack[7].m_obj;
lean_object* v___y_309_ = stack[8].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_301_, v_bi_302_, v_type_303_, v_k_304_, v_kind_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_330_, lean_object* v_bi_331_, lean_object* v_type_332_, lean_object* v_k_333_, lean_object* v_kind_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
uint8_t v_bi_boxed_340_; uint8_t v_kind_boxed_341_; lean_object* v_res_342_; 
v_bi_boxed_340_ = lean_unbox(v_bi_331_);
v_kind_boxed_341_ = lean_unbox(v_kind_334_);
v_res_342_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_330_, v_bi_boxed_340_, v_type_332_, v_k_333_, v_kind_boxed_341_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_342_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(lean_object* v_name_343_, lean_object* v_type_344_, lean_object* v_k_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; 
v___x_351_ = 0;
v___x_352_ = 0;
v___x_353_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_343_, v___x_351_, v_type_344_, v_k_345_, v___x_352_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_343_ = stack[0].m_obj;
lean_object* v_type_344_ = stack[1].m_obj;
lean_object* v_k_345_ = stack[2].m_obj;
lean_object* v___y_346_ = stack[3].m_obj;
lean_object* v___y_347_ = stack[4].m_obj;
lean_object* v___y_348_ = stack[5].m_obj;
lean_object* v___y_349_ = stack[6].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_343_, v_type_344_, v_k_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_355_, lean_object* v_type_356_, lean_object* v_k_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_355_, v_type_356_, v_k_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_eqs_367_, lean_object* v_kinds_368_, lean_object* v_xs_369_, lean_object* v_ys_370_, lean_object* v_k_371_, lean_object* v___x_372_, lean_object* v_h_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_367_, v_kinds_368_, v_xs_369_, v_ys_370_, v_k_371_, v___x_372_, v_h_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___x_372_);
return v_res_379_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(lean_object* v_eqs_380_, lean_object* v_kinds_381_, lean_object* v_xs_382_, lean_object* v_ys_383_, lean_object* v_k_384_, lean_object* v___x_385_, lean_object* v_h_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = lean_array_push(v_eqs_380_, v_h_386_);
v___x_393_ = 2;
v___x_394_ = lean_box(v___x_393_);
v___x_395_ = lean_array_push(v_kinds_381_, v___x_394_);
v___x_396_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_382_, v_ys_383_, v_k_384_, v___x_385_, v___x_392_, v___x_395_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_396_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqs_380_ = stack[0].m_obj;
lean_object* v_kinds_381_ = stack[1].m_obj;
lean_object* v_xs_382_ = stack[2].m_obj;
lean_object* v_ys_383_ = stack[3].m_obj;
lean_object* v_k_384_ = stack[4].m_obj;
lean_object* v___x_385_ = stack[5].m_obj;
lean_object* v_h_386_ = stack[6].m_obj;
lean_object* v___y_387_ = stack[7].m_obj;
lean_object* v___y_388_ = stack[8].m_obj;
lean_object* v___y_389_ = stack[9].m_obj;
lean_object* v___y_390_ = stack[10].m_obj;
lean_object* v_res_397_;
v_res_397_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_380_, v_kinds_381_, v_xs_382_, v_ys_383_, v_k_384_, v___x_385_, v_h_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed(lean_object* v_eqs_398_, lean_object* v_kinds_399_, lean_object* v_xs_400_, lean_object* v_ys_401_, lean_object* v_k_402_, lean_object* v___x_403_, lean_object* v_h_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1(v_eqs_398_, v_kinds_399_, v_xs_400_, v_ys_401_, v_k_402_, v___x_403_, v_h_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___x_403_);
return v_res_410_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(lean_object* v_xs_411_, lean_object* v_ys_412_, lean_object* v_k_413_, lean_object* v_i_414_, lean_object* v_eqs_415_, lean_object* v_kinds_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_array_get_size(v_xs_411_);
v___x_423_ = lean_nat_dec_lt(v_i_414_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_xs_411_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
v___x_424_ = lean_apply_7(v_k_413_, v_eqs_415_, v_kinds_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, lean_box(0));
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v_x_426_; lean_object* v_y_427_; lean_object* v___x_428_; 
v___x_425_ = l_Lean_instInhabitedExpr;
v_x_426_ = lean_array_get_borrowed(v___x_425_, v_xs_411_, v_i_414_);
v_y_427_ = lean_array_get_borrowed(v___x_425_, v_ys_412_, v_i_414_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
lean_inc(v_x_426_);
v___x_428_ = lean_infer_type(v_x_426_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = l_Lean_Expr_cleanupAnnotations(v_a_429_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
lean_inc(v_y_427_);
v___x_431_ = lean_infer_type(v_y_427_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = l_Lean_Expr_cleanupAnnotations(v_a_432_);
v___x_434_ = lean_expr_eqv(v___x_430_, v___x_433_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v___x_430_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_inc(v_y_427_);
lean_inc(v_x_426_);
v___x_435_ = l_Lean_Meta_mkHEq(v_x_426_, v_y_427_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_i_414_, v___x_438_);
lean_inc(v___x_439_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_440_, 0, v_eqs_415_);
lean_closure_set(v___f_440_, 1, v_kinds_416_);
lean_closure_set(v___f_440_, 2, v_xs_411_);
lean_closure_set(v___f_440_, 3, v_ys_412_);
lean_closure_set(v___f_440_, 4, v_k_413_);
lean_closure_set(v___f_440_, 5, v___x_439_);
v___x_441_ = lean_name_append_index_after(v___x_437_, v___x_439_);
v___x_442_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_441_, v_a_436_, v___f_440_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_kinds_416_);
lean_dec_ref(v_eqs_415_);
lean_dec_ref(v_k_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_xs_411_);
v_a_443_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_435_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_435_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v___x_451_; 
lean_inc(v_y_427_);
lean_inc(v_x_426_);
v___x_451_ = l_Lean_Meta_mkEq(v_x_426_, v_y_427_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___closed__1));
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_i_414_, v___x_454_);
lean_inc(v___x_455_);
v___f_456_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_456_, 0, v_eqs_415_);
lean_closure_set(v___f_456_, 1, v_kinds_416_);
lean_closure_set(v___f_456_, 2, v_xs_411_);
lean_closure_set(v___f_456_, 3, v_ys_412_);
lean_closure_set(v___f_456_, 4, v_k_413_);
lean_closure_set(v___f_456_, 5, v___x_455_);
v___x_457_ = lean_name_append_index_after(v___x_453_, v___x_455_);
v___x_458_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_457_, v_a_452_, v___f_456_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_kinds_416_);
lean_dec_ref(v_eqs_415_);
lean_dec_ref(v_k_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_xs_411_);
v_a_459_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_451_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_451_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v___x_430_);
lean_dec_ref(v_kinds_416_);
lean_dec_ref(v_eqs_415_);
lean_dec_ref(v_k_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_xs_411_);
v_a_467_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_431_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_431_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_kinds_416_);
lean_dec_ref(v_eqs_415_);
lean_dec_ref(v_k_413_);
lean_dec_ref(v_ys_412_);
lean_dec_ref(v_xs_411_);
v_a_475_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_428_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_428_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_411_ = stack[0].m_obj;
lean_object* v_ys_412_ = stack[1].m_obj;
lean_object* v_k_413_ = stack[2].m_obj;
lean_object* v_i_414_ = stack[3].m_obj;
lean_object* v_eqs_415_ = stack[4].m_obj;
lean_object* v_kinds_416_ = stack[5].m_obj;
lean_object* v_a_417_ = stack[6].m_obj;
lean_object* v_a_418_ = stack[7].m_obj;
lean_object* v_a_419_ = stack[8].m_obj;
lean_object* v_a_420_ = stack[9].m_obj;
lean_object* v_res_483_;
v_res_483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_411_, v_ys_412_, v_k_413_, v_i_414_, v_eqs_415_, v_kinds_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
stack->m_obj
 = v_res_483_;
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(lean_object* v_eqs_484_, lean_object* v_kinds_485_, lean_object* v_xs_486_, lean_object* v_ys_487_, lean_object* v_k_488_, lean_object* v___x_489_, lean_object* v_h_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_496_ = lean_array_push(v_eqs_484_, v_h_490_);
v___x_497_ = 4;
v___x_498_ = lean_box(v___x_497_);
v___x_499_ = lean_array_push(v_kinds_485_, v___x_498_);
v___x_500_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_486_, v_ys_487_, v_k_488_, v___x_489_, v___x_496_, v___x_499_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_500_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqs_484_ = stack[0].m_obj;
lean_object* v_kinds_485_ = stack[1].m_obj;
lean_object* v_xs_486_ = stack[2].m_obj;
lean_object* v_ys_487_ = stack[3].m_obj;
lean_object* v_k_488_ = stack[4].m_obj;
lean_object* v___x_489_ = stack[5].m_obj;
lean_object* v_h_490_ = stack[6].m_obj;
lean_object* v___y_491_ = stack[7].m_obj;
lean_object* v___y_492_ = stack[8].m_obj;
lean_object* v___y_493_ = stack[9].m_obj;
lean_object* v___y_494_ = stack[10].m_obj;
lean_object* v_res_501_;
v_res_501_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___lam__0(v_eqs_484_, v_kinds_485_, v_xs_486_, v_ys_487_, v_k_488_, v___x_489_, v_h_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg___boxed(lean_object* v_xs_502_, lean_object* v_ys_503_, lean_object* v_k_504_, lean_object* v_i_505_, lean_object* v_eqs_506_, lean_object* v_kinds_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_502_, v_ys_503_, v_k_504_, v_i_505_, v_eqs_506_, v_kinds_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_i_505_);
return v_res_513_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_object* v_00_u03b1_514_, lean_object* v_xs_515_, lean_object* v_ys_516_, lean_object* v_k_517_, lean_object* v_i_518_, lean_object* v_eqs_519_, lean_object* v_kinds_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_515_, v_ys_516_, v_k_517_, v_i_518_, v_eqs_519_, v_kinds_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
return v___x_526_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_515_ = stack[1].m_obj;
lean_object* v_ys_516_ = stack[2].m_obj;
lean_object* v_k_517_ = stack[3].m_obj;
lean_object* v_i_518_ = stack[4].m_obj;
lean_object* v_eqs_519_ = stack[5].m_obj;
lean_object* v_kinds_520_ = stack[6].m_obj;
lean_object* v_a_521_ = stack[7].m_obj;
lean_object* v_a_522_ = stack[8].m_obj;
lean_object* v_a_523_ = stack[9].m_obj;
lean_object* v_a_524_ = stack[10].m_obj;
lean_object* v_res_527_;
v_res_527_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(lean_box(0), v_xs_515_, v_ys_516_, v_k_517_, v_i_518_, v_eqs_519_, v_kinds_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___boxed(lean_object* v_00_u03b1_528_, lean_object* v_xs_529_, lean_object* v_ys_530_, lean_object* v_k_531_, lean_object* v_i_532_, lean_object* v_eqs_533_, lean_object* v_kinds_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop(v_00_u03b1_528_, v_xs_529_, v_ys_530_, v_k_531_, v_i_532_, v_eqs_533_, v_kinds_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_i_532_);
return v_res_540_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_541_, lean_object* v_name_542_, uint8_t v_bi_543_, lean_object* v_type_544_, lean_object* v_k_545_, uint8_t v_kind_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___redArg(v_name_542_, v_bi_543_, v_type_544_, v_k_545_, v_kind_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_552_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_542_ = stack[1].m_obj;
uint8_t v_bi_543_ = stack[2].m_num;
lean_object* v_type_544_ = stack[3].m_obj;
lean_object* v_k_545_ = stack[4].m_obj;
uint8_t v_kind_546_ = stack[5].m_num;
lean_object* v___y_547_ = stack[6].m_obj;
lean_object* v___y_548_ = stack[7].m_obj;
lean_object* v___y_549_ = stack[8].m_obj;
lean_object* v___y_550_ = stack[9].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(lean_box(0), v_name_542_, v_bi_543_, v_type_544_, v_k_545_, v_kind_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_554_, lean_object* v_name_555_, lean_object* v_bi_556_, lean_object* v_type_557_, lean_object* v_k_558_, lean_object* v_kind_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_bi_boxed_565_; uint8_t v_kind_boxed_566_; lean_object* v_res_567_; 
v_bi_boxed_565_ = lean_unbox(v_bi_556_);
v_kind_boxed_566_ = lean_unbox(v_kind_559_);
v_res_567_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_554_, v_name_555_, v_bi_boxed_565_, v_type_557_, v_k_558_, v_kind_boxed_566_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_567_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_568_, lean_object* v_name_569_, lean_object* v_type_570_, lean_object* v_k_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v_name_569_, v_type_570_, v_k_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_569_ = stack[1].m_obj;
lean_object* v_type_570_ = stack[2].m_obj;
lean_object* v_k_571_ = stack[3].m_obj;
lean_object* v___y_572_ = stack[4].m_obj;
lean_object* v___y_573_ = stack[5].m_obj;
lean_object* v___y_574_ = stack[6].m_obj;
lean_object* v___y_575_ = stack[7].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(lean_box(0), v_name_569_, v_type_570_, v_k_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_579_, lean_object* v_name_580_, lean_object* v_type_581_, lean_object* v_k_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0(v_00_u03b1_579_, v_name_580_, v_type_581_, v_k_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(lean_object* v_xs_591_, lean_object* v_ys_592_, lean_object* v_k_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_601_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop___redArg(v_xs_591_, v_ys_592_, v_k_593_, v___x_599_, v___x_600_, v___x_600_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_601_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_591_ = stack[0].m_obj;
lean_object* v_ys_592_ = stack[1].m_obj;
lean_object* v_k_593_ = stack[2].m_obj;
lean_object* v_a_594_ = stack[3].m_obj;
lean_object* v_a_595_ = stack[4].m_obj;
lean_object* v_a_596_ = stack[5].m_obj;
lean_object* v_a_597_ = stack[6].m_obj;
lean_object* v_res_602_;
v_res_602_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_591_, v_ys_592_, v_k_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___boxed(lean_object* v_xs_603_, lean_object* v_ys_604_, lean_object* v_k_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_603_, v_ys_604_, v_k_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_611_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_object* v_00_u03b1_612_, lean_object* v_xs_613_, lean_object* v_ys_614_, lean_object* v_k_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg(v_xs_613_, v_ys_614_, v_k_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_621_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_613_ = stack[1].m_obj;
lean_object* v_ys_614_ = stack[2].m_obj;
lean_object* v_k_615_ = stack[3].m_obj;
lean_object* v_a_616_ = stack[4].m_obj;
lean_object* v_a_617_ = stack[5].m_obj;
lean_object* v_a_618_ = stack[6].m_obj;
lean_object* v_a_619_ = stack[7].m_obj;
lean_object* v_res_622_;
v_res_622_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(lean_box(0), v_xs_613_, v_ys_614_, v_k_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed(lean_object* v_00_u03b1_623_, lean_object* v_xs_624_, lean_object* v_ys_625_, lean_object* v_k_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs(v_00_u03b1_623_, v_xs_624_, v_ys_625_, v_k_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(lean_object* v_k_633_, lean_object* v_b_634_, lean_object* v_c_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
v___x_641_ = lean_apply_7(v_k_633_, v_b_634_, v_c_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, lean_box(0));
return v___x_641_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_633_ = stack[0].m_obj;
lean_object* v_b_634_ = stack[1].m_obj;
lean_object* v_c_635_ = stack[2].m_obj;
lean_object* v___y_636_ = stack[3].m_obj;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v___y_639_ = stack[6].m_obj;
lean_object* v_res_642_;
v_res_642_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_633_, v_b_634_, v_c_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
stack->m_obj
 = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed(lean_object* v_k_643_, lean_object* v_b_644_, lean_object* v_c_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0(v_k_643_, v_b_644_, v_c_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(lean_object* v_type_652_, lean_object* v_maxFVars_x3f_653_, lean_object* v_k_654_, uint8_t v_cleanupAnnotations_655_, uint8_t v_whnfType_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___f_662_; lean_object* v___x_663_; 
v___f_662_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_662_, 0, v_k_654_);
v___x_663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_652_, v_maxFVars_x3f_653_, v___f_662_, v_cleanupAnnotations_655_, v_whnfType_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_663_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_652_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_653_ = stack[1].m_obj;
lean_object* v_k_654_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_655_ = stack[3].m_num;
uint8_t v_whnfType_656_ = stack[4].m_num;
lean_object* v___y_657_ = stack[5].m_obj;
lean_object* v___y_658_ = stack[6].m_obj;
lean_object* v___y_659_ = stack[7].m_obj;
lean_object* v___y_660_ = stack[8].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_652_, v_maxFVars_x3f_653_, v_k_654_, v_cleanupAnnotations_655_, v_whnfType_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___boxed(lean_object* v_type_681_, lean_object* v_maxFVars_x3f_682_, lean_object* v_k_683_, lean_object* v_cleanupAnnotations_684_, lean_object* v_whnfType_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_691_; uint8_t v_whnfType_boxed_692_; lean_object* v_res_693_; 
v_cleanupAnnotations_boxed_691_ = lean_unbox(v_cleanupAnnotations_684_);
v_whnfType_boxed_692_ = lean_unbox(v_whnfType_685_);
v_res_693_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_681_, v_maxFVars_x3f_682_, v_k_683_, v_cleanupAnnotations_boxed_691_, v_whnfType_boxed_692_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_693_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_object* v_00_u03b1_694_, lean_object* v_type_695_, lean_object* v_maxFVars_x3f_696_, lean_object* v_k_697_, uint8_t v_cleanupAnnotations_698_, uint8_t v_whnfType_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_695_, v_maxFVars_x3f_696_, v_k_697_, v_cleanupAnnotations_698_, v_whnfType_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_695_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_696_ = stack[2].m_obj;
lean_object* v_k_697_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_698_ = stack[4].m_num;
uint8_t v_whnfType_699_ = stack[5].m_num;
lean_object* v___y_700_ = stack[6].m_obj;
lean_object* v___y_701_ = stack[7].m_obj;
lean_object* v___y_702_ = stack[8].m_obj;
lean_object* v___y_703_ = stack[9].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(lean_box(0), v_type_695_, v_maxFVars_x3f_696_, v_k_697_, v_cleanupAnnotations_698_, v_whnfType_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___boxed(lean_object* v_00_u03b1_707_, lean_object* v_type_708_, lean_object* v_maxFVars_x3f_709_, lean_object* v_k_710_, lean_object* v_cleanupAnnotations_711_, lean_object* v_whnfType_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_718_; uint8_t v_whnfType_boxed_719_; lean_object* v_res_720_; 
v_cleanupAnnotations_boxed_718_ = lean_unbox(v_cleanupAnnotations_711_);
v_whnfType_boxed_719_ = lean_unbox(v_whnfType_712_);
v_res_720_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0(v_00_u03b1_707_, v_type_708_, v_maxFVars_x3f_709_, v_k_710_, v_cleanupAnnotations_boxed_718_, v_whnfType_boxed_719_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed(lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v_a_734_, lean_object* v_type_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_1796__boxed_741_; lean_object* v_res_742_; 
v___x_1796__boxed_741_ = lean_unbox(v___x_731_);
v_res_742_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_729_, v___x_730_, v___x_1796__boxed_741_, v___x_732_, v___x_733_, v_a_734_, v_type_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_a_734_);
return v_res_742_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(lean_object* v_type_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_750_ = lean_unsigned_to_nat(3u);
v___x_751_ = l_Lean_Expr_isAppOfArity(v_type_743_, v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__3));
v___x_753_ = lean_unsigned_to_nat(4u);
v___x_754_ = l_Lean_Expr_isAppOfArity(v_type_743_, v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___f_759_; uint8_t v___x_760_; lean_object* v___x_761_; 
v___x_755_ = l_Lean_instInhabitedExpr;
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_758_ = lean_box(v___x_754_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2___boxed), 12, 5);
lean_closure_set(v___f_759_, 0, v___x_755_);
lean_closure_set(v___f_759_, 1, v___x_756_);
lean_closure_set(v___f_759_, 2, v___x_758_);
lean_closure_set(v___f_759_, 3, v___x_750_);
lean_closure_set(v___f_759_, 4, v___x_757_);
v___x_760_ = 1;
v___x_761_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_743_, v___x_757_, v___f_759_, v___x_760_, v___x_754_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = l_Lean_Expr_appFn_x21(v_type_743_);
lean_dec_ref(v_type_743_);
v___x_763_ = l_Lean_Expr_appFn_x21(v___x_762_);
lean_dec_ref(v___x_762_);
v___x_764_ = l_Lean_Expr_appArg_x21(v___x_763_);
lean_dec_ref(v___x_763_);
v___x_765_ = l_Lean_Meta_mkHEqRefl(v___x_764_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_765_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = l_Lean_Expr_appFn_x21(v_type_743_);
lean_dec_ref(v_type_743_);
v___x_767_ = l_Lean_Expr_appArg_x21(v___x_766_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Lean_Meta_mkEqRefl(v___x_767_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_768_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_743_ = stack[0].m_obj;
lean_object* v_a_744_ = stack[1].m_obj;
lean_object* v_a_745_ = stack[2].m_obj;
lean_object* v_a_746_ = stack[3].m_obj;
lean_object* v_a_747_ = stack[4].m_obj;
lean_object* v_res_769_;
v_res_769_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
stack->m_obj
 = v_res_769_;
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(lean_object* v_type_770_, lean_object* v_motive_771_, lean_object* v___x_772_, lean_object* v_b_773_, uint8_t v___x_774_, lean_object* v___x_775_, lean_object* v_a_776_, lean_object* v_eqPr_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_type_783_; lean_object* v_motive_784_; lean_object* v___x_785_; 
v_type_783_ = l_Lean_Expr_bindingBody_x21(v_type_770_);
v_motive_784_ = l_Lean_Expr_bindingBody_x21(v_motive_771_);
v___x_785_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_783_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_major_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___x_806_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc_ref(v_eqPr_777_);
v___x_806_ = lean_infer_type(v_eqPr_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
v___x_808_ = lean_whnf(v_a_807_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; uint8_t v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = l_Lean_Expr_isHEq(v_a_809_);
lean_dec(v_a_809_);
if (v___x_810_ == 0)
{
lean_inc_ref(v_eqPr_777_);
v_major_788_ = v_eqPr_777_;
v___y_789_ = v___y_778_;
v___y_790_ = v___y_779_;
v___y_791_ = v___y_780_;
v___y_792_ = v___y_781_;
goto v___jp_787_;
}
else
{
lean_object* v___x_811_; 
lean_inc_ref(v_eqPr_777_);
v___x_811_ = l_Lean_Meta_mkEqOfHEq(v_eqPr_777_, v___x_810_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v_major_788_ = v_a_812_;
v___y_789_ = v___y_778_;
v___y_790_ = v___y_779_;
v___y_791_ = v___y_780_;
v___y_792_ = v___y_781_;
goto v___jp_787_;
}
else
{
lean_dec(v_a_786_);
lean_dec_ref(v_motive_784_);
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_811_;
}
}
}
else
{
lean_dec(v_a_786_);
lean_dec_ref(v_motive_784_);
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_808_;
}
}
else
{
lean_dec(v_a_786_);
lean_dec_ref(v_motive_784_);
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_806_;
}
v___jp_787_:
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; 
v___x_793_ = lean_mk_empty_array_with_capacity(v___x_772_);
lean_inc_ref(v_b_773_);
v___x_794_ = lean_array_push(v___x_793_, v_b_773_);
v___x_795_ = 1;
v___x_796_ = 1;
v___x_797_ = l_Lean_Meta_mkLambdaFVars(v___x_794_, v_motive_784_, v___x_774_, v___x_795_, v___x_774_, v___x_795_, v___x_796_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec_ref(v___x_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = l_Lean_Meta_mkEqNDRec(v_a_798_, v_a_786_, v_major_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_775_);
v___x_802_ = lean_array_push(v___x_801_, v_a_776_);
v___x_803_ = lean_array_push(v___x_802_, v_b_773_);
v___x_804_ = lean_array_push(v___x_803_, v_eqPr_777_);
v___x_805_ = l_Lean_Meta_mkLambdaFVars(v___x_804_, v_a_800_, v___x_774_, v___x_795_, v___x_774_, v___x_795_, v___x_796_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec_ref(v___x_804_);
return v___x_805_;
}
else
{
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_799_;
}
}
else
{
lean_dec_ref(v_major_788_);
lean_dec(v_a_786_);
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_797_;
}
}
}
else
{
lean_dec_ref(v_motive_784_);
lean_dec_ref(v_eqPr_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_b_773_);
return v___x_785_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_770_ = stack[0].m_obj;
lean_object* v_motive_771_ = stack[1].m_obj;
lean_object* v___x_772_ = stack[2].m_obj;
lean_object* v_b_773_ = stack[3].m_obj;
uint8_t v___x_774_ = stack[4].m_num;
lean_object* v___x_775_ = stack[5].m_obj;
lean_object* v_a_776_ = stack[6].m_obj;
lean_object* v_eqPr_777_ = stack[7].m_obj;
lean_object* v___y_778_ = stack[8].m_obj;
lean_object* v___y_779_ = stack[9].m_obj;
lean_object* v___y_780_ = stack[10].m_obj;
lean_object* v___y_781_ = stack[11].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_770_, v_motive_771_, v___x_772_, v_b_773_, v___x_774_, v___x_775_, v_a_776_, v_eqPr_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed(lean_object* v_type_814_, lean_object* v_motive_815_, lean_object* v___x_816_, lean_object* v_b_817_, lean_object* v___x_818_, lean_object* v___x_819_, lean_object* v_a_820_, lean_object* v_eqPr_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_1852__boxed_827_; lean_object* v_res_828_; 
v___x_1852__boxed_827_ = lean_unbox(v___x_818_);
v_res_828_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0(v_type_814_, v_motive_815_, v___x_816_, v_b_817_, v___x_1852__boxed_827_, v___x_819_, v_a_820_, v_eqPr_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___x_819_);
lean_dec(v___x_816_);
lean_dec_ref(v_motive_815_);
lean_dec_ref(v_type_814_);
return v_res_828_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_type_831_, lean_object* v_a_832_, lean_object* v___x_833_, uint8_t v___x_834_, lean_object* v___x_835_, lean_object* v_b_836_, lean_object* v_motive_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_b_843_; lean_object* v___x_844_; lean_object* v_type_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_b_843_ = lean_array_get_borrowed(v___x_829_, v_b_836_, v___x_830_);
v___x_844_ = l_Lean_Expr_bindingBody_x21(v_type_831_);
v_type_845_ = lean_expr_instantiate1(v___x_844_, v_a_832_);
lean_dec_ref(v___x_844_);
v___x_846_ = lean_box(v___x_834_);
lean_inc(v_b_843_);
lean_inc_ref(v_motive_837_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__0___boxed), 13, 7);
lean_closure_set(v___f_847_, 0, v_type_845_);
lean_closure_set(v___f_847_, 1, v_motive_837_);
lean_closure_set(v___f_847_, 2, v___x_833_);
lean_closure_set(v___f_847_, 3, v_b_843_);
lean_closure_set(v___f_847_, 4, v___x_846_);
lean_closure_set(v___f_847_, 5, v___x_835_);
lean_closure_set(v___f_847_, 6, v_a_832_);
v___x_848_ = l_Lean_Expr_bindingName_x21(v_motive_837_);
v___x_849_ = l_Lean_Expr_bindingDomain_x21(v_motive_837_);
lean_dec_ref(v_motive_837_);
v___x_850_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_848_, v___x_849_, v___f_847_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_829_ = stack[0].m_obj;
lean_object* v___x_830_ = stack[1].m_obj;
lean_object* v_type_831_ = stack[2].m_obj;
lean_object* v_a_832_ = stack[3].m_obj;
lean_object* v___x_833_ = stack[4].m_obj;
uint8_t v___x_834_ = stack[5].m_num;
lean_object* v___x_835_ = stack[6].m_obj;
lean_object* v_b_836_ = stack[7].m_obj;
lean_object* v_motive_837_ = stack[8].m_obj;
lean_object* v___y_838_ = stack[9].m_obj;
lean_object* v___y_839_ = stack[10].m_obj;
lean_object* v___y_840_ = stack[11].m_obj;
lean_object* v___y_841_ = stack[12].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_829_, v___x_830_, v_type_831_, v_a_832_, v___x_833_, v___x_834_, v___x_835_, v_b_836_, v_motive_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed(lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_type_854_, lean_object* v_a_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v_b_859_, lean_object* v_motive_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_1811__boxed_866_; lean_object* v_res_867_; 
v___x_1811__boxed_866_ = lean_unbox(v___x_857_);
v_res_867_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1(v___x_852_, v___x_853_, v_type_854_, v_a_855_, v___x_856_, v___x_1811__boxed_866_, v___x_858_, v_b_859_, v_motive_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec_ref(v_b_859_);
lean_dec_ref(v_type_854_);
lean_dec(v___x_853_);
lean_dec_ref(v___x_852_);
return v_res_867_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(lean_object* v___x_868_, lean_object* v___x_869_, uint8_t v___x_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_a_873_, lean_object* v_type_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___f_883_; uint8_t v___x_884_; lean_object* v___x_885_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v_a_881_ = lean_array_get(v___x_868_, v_a_873_, v___x_880_);
v___x_882_ = lean_box(v___x_870_);
lean_inc_ref(v_type_874_);
v___f_883_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__1___boxed), 14, 7);
lean_closure_set(v___f_883_, 0, v___x_868_);
lean_closure_set(v___f_883_, 1, v___x_880_);
lean_closure_set(v___f_883_, 2, v_type_874_);
lean_closure_set(v___f_883_, 3, v_a_881_);
lean_closure_set(v___f_883_, 4, v___x_869_);
lean_closure_set(v___f_883_, 5, v___x_882_);
lean_closure_set(v___f_883_, 6, v___x_871_);
v___x_884_ = 1;
v___x_885_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_874_, v___x_872_, v___f_883_, v___x_884_, v___x_870_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_885_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_868_ = stack[0].m_obj;
lean_object* v___x_869_ = stack[1].m_obj;
uint8_t v___x_870_ = stack[2].m_num;
lean_object* v___x_871_ = stack[3].m_obj;
lean_object* v___x_872_ = stack[4].m_obj;
lean_object* v_a_873_ = stack[5].m_obj;
lean_object* v_type_874_ = stack[6].m_obj;
lean_object* v___y_875_ = stack[7].m_obj;
lean_object* v___y_876_ = stack[8].m_obj;
lean_object* v___y_877_ = stack[9].m_obj;
lean_object* v___y_878_ = stack[10].m_obj;
lean_object* v_res_886_;
v_res_886_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___lam__2(v___x_868_, v___x_869_, v___x_870_, v___x_871_, v___x_872_, v_a_873_, v_type_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___boxed(lean_object* v_type_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_type_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_893_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(lean_object* v_lctx_894_, lean_object* v_localInsts_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_894_, v_localInsts_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_902_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_902_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_894_ = stack[0].m_obj;
lean_object* v_localInsts_895_ = stack[1].m_obj;
lean_object* v_x_896_ = stack[2].m_obj;
lean_object* v___y_897_ = stack[3].m_obj;
lean_object* v___y_898_ = stack[4].m_obj;
lean_object* v___y_899_ = stack[5].m_obj;
lean_object* v___y_900_ = stack[6].m_obj;
lean_object* v_res_919_;
v_res_919_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_894_, v_localInsts_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg___boxed(lean_object* v_lctx_920_, lean_object* v_localInsts_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_920_, v_localInsts_921_, v_x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_object* v_00_u03b1_929_, lean_object* v_lctx_930_, lean_object* v_localInsts_931_, lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v_lctx_930_, v_localInsts_931_, v_x_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_930_ = stack[1].m_obj;
lean_object* v_localInsts_931_ = stack[2].m_obj;
lean_object* v_x_932_ = stack[3].m_obj;
lean_object* v___y_933_ = stack[4].m_obj;
lean_object* v___y_934_ = stack[5].m_obj;
lean_object* v___y_935_ = stack[6].m_obj;
lean_object* v___y_936_ = stack[7].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(lean_box(0), v_lctx_930_, v_localInsts_931_, v_x_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___boxed(lean_object* v_00_u03b1_940_, lean_object* v_lctx_941_, lean_object* v_localInsts_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2(v_00_u03b1_940_, v_lctx_941_, v_localInsts_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_949_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(lean_object* v_as_950_, size_t v_sz_951_, size_t v_i_952_, lean_object* v_b_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_952_, v_sz_951_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_953_);
return v___x_956_;
}
else
{
lean_object* v_snd_957_; lean_object* v_snd_958_; lean_object* v_fst_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1029_; 
v_snd_957_ = lean_ctor_get(v_b_953_, 1);
lean_inc(v_snd_957_);
v_snd_958_ = lean_ctor_get(v_snd_957_, 1);
lean_inc(v_snd_958_);
v_fst_959_ = lean_ctor_get(v_b_953_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_b_953_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_b_953_, 1);
lean_dec(v_unused_1030_);
v___x_961_ = v_b_953_;
v_isShared_962_ = v_isSharedCheck_1029_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_fst_959_);
lean_dec(v_b_953_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1029_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_fst_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1027_; 
v_fst_963_ = lean_ctor_get(v_snd_957_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_snd_957_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_snd_957_, 1);
lean_dec(v_unused_1028_);
v___x_965_ = v_snd_957_;
v_isShared_966_ = v_isSharedCheck_1027_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_fst_963_);
lean_dec(v_snd_957_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1027_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_array_967_; lean_object* v_start_968_; lean_object* v_stop_969_; uint8_t v___x_970_; 
v_array_967_ = lean_ctor_get(v_snd_958_, 0);
v_start_968_ = lean_ctor_get(v_snd_958_, 1);
v_stop_969_ = lean_ctor_get(v_snd_958_, 2);
v___x_970_ = lean_nat_dec_lt(v_start_968_, v_stop_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_972_; 
if (v_isShared_966_ == 0)
{
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_snd_958_);
v___x_972_ = v_reuseFailAlloc_977_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_972_);
v___x_974_ = v___x_961_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fst_959_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
else
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1023_; 
lean_inc(v_stop_969_);
lean_inc(v_start_968_);
lean_inc_ref(v_array_967_);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_snd_958_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1024_ = lean_ctor_get(v_snd_958_, 2);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_snd_958_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_snd_958_, 0);
lean_dec(v_unused_1026_);
v___x_979_ = v_snd_958_;
v_isShared_980_ = v_isSharedCheck_1023_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_snd_958_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1023_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_array_981_; lean_object* v_start_982_; lean_object* v_stop_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v_array_981_ = lean_ctor_get(v_fst_963_, 0);
v_start_982_ = lean_ctor_get(v_fst_963_, 1);
v_stop_983_ = lean_ctor_get(v_fst_963_, 2);
v___x_984_ = lean_array_fget(v_array_967_, v_start_968_);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_start_968_, v___x_985_);
lean_dec(v_start_968_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_array_967_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_stop_969_);
v___x_988_ = v_reuseFailAlloc_1022_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_lt(v_start_982_, v_stop_983_);
if (v___x_989_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v___x_984_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v___x_988_);
v___x_991_ = v___x_965_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_fst_963_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_988_);
v___x_991_ = v_reuseFailAlloc_996_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_991_);
v___x_993_ = v___x_961_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_959_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
else
{
lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1018_; 
lean_inc(v_stop_983_);
lean_inc(v_start_982_);
lean_inc_ref(v_array_981_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_fst_963_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; lean_object* v_unused_1021_; 
v_unused_1019_ = lean_ctor_get(v_fst_963_, 2);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_fst_963_, 1);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_fst_963_, 0);
lean_dec(v_unused_1021_);
v___x_998_ = v_fst_963_;
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
else
{
lean_dec(v_fst_963_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v_a_1000_ = lean_array_uget_borrowed(v_as_950_, v_i_952_);
v___x_1001_ = lean_array_fget(v_array_981_, v_start_982_);
v___x_1002_ = lean_nat_add(v_start_982_, v___x_985_);
lean_dec(v_start_982_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1002_);
v___x_1004_ = v___x_998_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_array_981_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_stop_983_);
v___x_1004_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_inc(v_a_1000_);
v___x_1005_ = lean_array_push(v_fst_959_, v_a_1000_);
v___x_1006_ = lean_array_push(v___x_1005_, v___x_1001_);
v___x_1007_ = lean_array_push(v___x_1006_, v___x_984_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v___x_988_);
lean_ctor_set(v___x_965_, 0, v___x_1004_);
v___x_1009_ = v___x_965_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_988_);
v___x_1009_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_1009_);
lean_ctor_set(v___x_961_, 0, v___x_1007_);
v___x_1011_ = v___x_961_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
size_t v___x_1012_; size_t v___x_1013_; 
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_add(v_i_952_, v___x_1012_);
v_i_952_ = v___x_1013_;
v_b_953_ = v___x_1011_;
goto _start;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_950_ = stack[0].m_obj;
size_t v_sz_951_ = stack[1].m_num;
size_t v_i_952_ = stack[2].m_num;
lean_object* v_b_953_ = stack[3].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_950_, v_sz_951_, v_i_952_, v_b_953_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg___boxed(lean_object* v_as_1032_, lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1032_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1035_);
lean_dec_ref(v_as_1032_);
return v_res_1039_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0(lean_object* v_ys_1040_, lean_object* v_xs_1041_, lean_object* v_f_1042_, uint8_t v___x_1043_, uint8_t v___x_1044_, lean_object* v_eqs_1045_, lean_object* v_argKinds_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_1054_ = lean_array_get_size(v_ys_1040_);
lean_inc_ref(v_ys_1040_);
v___x_1055_ = l_Array_toSubarray___redArg(v_ys_1040_, v___x_1052_, v___x_1054_);
v___x_1056_ = lean_array_get_size(v_eqs_1045_);
v___x_1057_ = l_Array_toSubarray___redArg(v_eqs_1045_, v___x_1052_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1055_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1053_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v_sz_1060_ = lean_array_size(v_xs_1041_);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_xs_1041_, v_sz_1060_, v___x_1061_, v___x_1059_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v_fst_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v_fst_1064_ = lean_ctor_get(v_a_1063_, 0);
lean_inc(v_fst_1064_);
lean_dec(v_a_1063_);
lean_inc_ref(v_f_1042_);
v___x_1065_ = l_Lean_mkAppN(v_f_1042_, v_xs_1041_);
v___x_1066_ = l_Lean_mkAppN(v_f_1042_, v_ys_1040_);
lean_dec_ref(v_ys_1040_);
v___x_1067_ = l_Lean_Meta_mkHEq(v___x_1065_, v___x_1066_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = 1;
v___x_1070_ = l_Lean_Meta_mkForallFVars(v_fst_1064_, v_a_1068_, v___x_1043_, v___x_1044_, v___x_1044_, v___x_1069_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v_fst_1064_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_n(v_a_1071_, 2);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof(v_a_1071_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1077_, 0, v_a_1071_);
lean_ctor_set(v___x_1077_, 1, v_a_1073_);
lean_ctor_set(v___x_1077_, 2, v_argKinds_1046_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1071_);
lean_dec_ref(v_argKinds_1046_);
v_a_1082_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1072_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1072_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_argKinds_1046_);
v_a_1090_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1070_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1070_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_fst_1064_);
lean_dec_ref(v_argKinds_1046_);
v_a_1098_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1067_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1067_);
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
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_argKinds_1046_);
lean_dec_ref(v_f_1042_);
lean_dec_ref(v_ys_1040_);
v_a_1106_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1062_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1062_);
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
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArity___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_1040_ = stack[0].m_obj;
lean_object* v_xs_1041_ = stack[1].m_obj;
lean_object* v_f_1042_ = stack[2].m_obj;
uint8_t v___x_1043_ = stack[3].m_num;
uint8_t v___x_1044_ = stack[4].m_num;
lean_object* v_eqs_1045_ = stack[5].m_obj;
lean_object* v_argKinds_1046_ = stack[6].m_obj;
lean_object* v___y_1047_ = stack[7].m_obj;
lean_object* v___y_1048_ = stack[8].m_obj;
lean_object* v___y_1049_ = stack[9].m_obj;
lean_object* v___y_1050_ = stack[10].m_obj;
lean_object* v_res_1114_;
v_res_1114_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1040_, v_xs_1041_, v_f_1042_, v___x_1043_, v___x_1044_, v_eqs_1045_, v_argKinds_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
stack->m_obj
 = v_res_1114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__0___boxed(lean_object* v_ys_1115_, lean_object* v_xs_1116_, lean_object* v_f_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_eqs_1120_, lean_object* v_argKinds_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_4657__boxed_1127_; uint8_t v___x_4658__boxed_1128_; lean_object* v_res_1129_; 
v___x_4657__boxed_1127_ = lean_unbox(v___x_1118_);
v___x_4658__boxed_1128_ = lean_unbox(v___x_1119_);
v_res_1129_ = l_Lean_Meta_mkHCongrWithArity___lam__0(v_ys_1115_, v_xs_1116_, v_f_1117_, v___x_4657__boxed_1127_, v___x_4658__boxed_1128_, v_eqs_1120_, v_argKinds_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v_xs_1116_);
return v_res_1129_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(lean_object* v_msgData_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v_env_1137_; uint8_t v___x_1138_; lean_object* v_env_1139_; lean_object* v___x_1140_; lean_object* v_toCold_1141_; lean_object* v_mctx_1142_; lean_object* v_lctx_1143_; lean_object* v_options_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1136_ = lean_st_ref_get(v___y_1134_);
v_env_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc_ref(v_env_1137_);
lean_dec(v___x_1136_);
v___x_1138_ = 0;
v_env_1139_ = l_Lean_Environment_setRecordingDeps(v_env_1137_, v___x_1138_);
v___x_1140_ = lean_st_ref_get(v___y_1132_);
v_toCold_1141_ = lean_ctor_get(v___y_1133_, 0);
v_mctx_1142_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_mctx_1142_);
lean_dec(v___x_1140_);
v_lctx_1143_ = lean_ctor_get(v___y_1131_, 2);
v_options_1144_ = lean_ctor_get(v_toCold_1141_, 2);
lean_inc_ref(v_options_1144_);
lean_inc_ref(v_lctx_1143_);
v___x_1145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1145_, 0, v_env_1139_);
lean_ctor_set(v___x_1145_, 1, v_mctx_1142_);
lean_ctor_set(v___x_1145_, 2, v_lctx_1143_);
lean_ctor_set(v___x_1145_, 3, v_options_1144_);
v___x_1146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v_msgData_1130_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1130_ = stack[0].m_obj;
lean_object* v___y_1131_ = stack[1].m_obj;
lean_object* v___y_1132_ = stack[2].m_obj;
lean_object* v___y_1133_ = stack[3].m_obj;
lean_object* v___y_1134_ = stack[4].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0___boxed(lean_object* v_msgData_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msgData_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_ref_1162_; lean_object* v___x_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_ref_1162_ = lean_ctor_get(v___y_1159_, 2);
v___x_1163_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_inc(v_ref_1162_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_ref_1162_);
lean_ctor_set(v___x_1168_, 1, v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 1);
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1156_ = stack[0].m_obj;
lean_object* v___y_1157_ = stack[1].m_obj;
lean_object* v___y_1158_ = stack[2].m_obj;
lean_object* v___y_1159_ = stack[3].m_obj;
lean_object* v___y_1160_ = stack[4].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg___boxed(lean_object* v_msg_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__0));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__2));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArity___lam__1___closed__4));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1(lean_object* v_xs_1190_, lean_object* v_numArgs_1191_, lean_object* v_f_1192_, lean_object* v_ys_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_array_get_size(v_xs_1190_);
v___x_1201_ = lean_nat_dec_eq(v___x_1200_, v_numArgs_1191_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_ys_1193_);
lean_dec_ref(v_xs_1190_);
v___x_1202_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__1);
v___x_1203_ = l_Nat_reprFast(v_numArgs_1191_);
v___x_1204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = l_Lean_MessageData_ofFormat(v___x_1204_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1202_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__3);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Nat_reprFast(v___x_1200_);
v___x_1210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = l_Lean_MessageData_ofFormat(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1208_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5, &l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5_once, _init_l_Lean_Meta_mkHCongrWithArity___lam__1___closed__5);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_indentExpr(v_f_1192_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v___x_1216_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1217_;
}
else
{
lean_object* v_lctx_1218_; lean_object* v_localInstances_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v_numArgs_1191_);
v_lctx_1218_ = lean_ctor_get(v___y_1195_, 2);
v_localInstances_1219_ = lean_ctor_get(v___y_1195_, 3);
v___x_1220_ = 0;
v___x_1221_ = lean_box(v___x_1220_);
v___x_1222_ = lean_box(v___x_1201_);
lean_inc_ref(v_xs_1190_);
lean_inc_ref(v_ys_1193_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1223_, 0, v_ys_1193_);
lean_closure_set(v___f_1223_, 1, v_xs_1190_);
lean_closure_set(v___f_1223_, 2, v_f_1192_);
lean_closure_set(v___f_1223_, 3, v___x_1221_);
lean_closure_set(v___f_1223_, 4, v___x_1222_);
lean_inc_ref(v_lctx_1218_);
v___x_1224_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_addPrimeToFVarUserNames(v_ys_1193_, v_lctx_1218_);
v___x_1225_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_ys_1193_, v___x_1224_);
v___x_1226_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_setBinderInfosD(v_xs_1190_, v___x_1225_);
v___x_1227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___boxed), 9, 4);
lean_closure_set(v___x_1227_, 0, lean_box(0));
lean_closure_set(v___x_1227_, 1, v_xs_1190_);
lean_closure_set(v___x_1227_, 2, v_ys_1193_);
lean_closure_set(v___x_1227_, 3, v___f_1223_);
lean_inc_ref(v_localInstances_1219_);
v___x_1228_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkHCongrWithArity_spec__2___redArg(v___x_1226_, v_localInstances_1219_, v___x_1227_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1228_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArity___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1190_ = stack[0].m_obj;
lean_object* v_numArgs_1191_ = stack[1].m_obj;
lean_object* v_f_1192_ = stack[2].m_obj;
lean_object* v_ys_1193_ = stack[3].m_obj;
lean_object* v_x_1194_ = stack[4].m_obj;
lean_object* v___y_1195_ = stack[5].m_obj;
lean_object* v___y_1196_ = stack[6].m_obj;
lean_object* v___y_1197_ = stack[7].m_obj;
lean_object* v___y_1198_ = stack[8].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1190_, v_numArgs_1191_, v_f_1192_, v_ys_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__1___boxed(lean_object* v_xs_1230_, lean_object* v_numArgs_1231_, lean_object* v_f_1232_, lean_object* v_ys_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Meta_mkHCongrWithArity___lam__1(v_xs_1230_, v_numArgs_1231_, v_f_1232_, v_ys_1233_, v_x_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v_x_1234_);
return v_res_1240_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2(lean_object* v_numArgs_1241_, lean_object* v_f_1242_, lean_object* v_a_1243_, lean_object* v___x_1244_, lean_object* v_xs_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___f_1252_; uint8_t v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; 
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1252_, 0, v_xs_1245_);
lean_closure_set(v___f_1252_, 1, v_numArgs_1241_);
lean_closure_set(v___f_1252_, 2, v_f_1242_);
v___x_1253_ = 1;
v___x_1254_ = 0;
v___x_1255_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1243_, v___x_1244_, v___f_1252_, v___x_1253_, v___x_1254_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1255_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArity___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numArgs_1241_ = stack[0].m_obj;
lean_object* v_f_1242_ = stack[1].m_obj;
lean_object* v_a_1243_ = stack[2].m_obj;
lean_object* v___x_1244_ = stack[3].m_obj;
lean_object* v_xs_1245_ = stack[4].m_obj;
lean_object* v_x_1246_ = stack[5].m_obj;
lean_object* v___y_1247_ = stack[6].m_obj;
lean_object* v___y_1248_ = stack[7].m_obj;
lean_object* v___y_1249_ = stack[8].m_obj;
lean_object* v___y_1250_ = stack[9].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1241_, v_f_1242_, v_a_1243_, v___x_1244_, v_xs_1245_, v_x_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___lam__2___boxed(lean_object* v_numArgs_1257_, lean_object* v_f_1258_, lean_object* v_a_1259_, lean_object* v___x_1260_, lean_object* v_xs_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_mkHCongrWithArity___lam__2(v_numArgs_1257_, v_f_1258_, v_a_1259_, v___x_1260_, v_xs_1261_, v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_x_1262_);
return v_res_1268_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object* v_f_1269_, lean_object* v_numArgs_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
lean_inc(v_a_1272_);
lean_inc_ref(v_a_1271_);
lean_inc_ref(v_f_1269_);
v___x_1276_ = lean_infer_type(v_f_1269_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; uint8_t v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_n(v_a_1277_, 2);
lean_dec_ref_known(v___x_1276_, 1);
lean_inc(v_numArgs_1270_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_numArgs_1270_);
lean_inc_ref(v___x_1278_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Meta_mkHCongrWithArity___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1279_, 0, v_numArgs_1270_);
lean_closure_set(v___f_1279_, 1, v_f_1269_);
lean_closure_set(v___f_1279_, 2, v_a_1277_);
lean_closure_set(v___f_1279_, 3, v___x_1278_);
v___x_1280_ = 1;
v___x_1281_ = 0;
v___x_1282_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_1277_, v___x_1278_, v___f_1279_, v___x_1280_, v___x_1281_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_numArgs_1270_);
lean_dec_ref(v_f_1269_);
v_a_1283_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1276_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1276_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArity_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1269_ = stack[0].m_obj;
lean_object* v_numArgs_1270_ = stack[1].m_obj;
lean_object* v_a_1271_ = stack[2].m_obj;
lean_object* v_a_1272_ = stack[3].m_obj;
lean_object* v_a_1273_ = stack[4].m_obj;
lean_object* v_a_1274_ = stack[5].m_obj;
lean_object* v_res_1291_;
v_res_1291_ = l_Lean_Meta_mkHCongrWithArity(v_f_1269_, v_numArgs_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArity___boxed(lean_object* v_f_1292_, lean_object* v_numArgs_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_mkHCongrWithArity(v_f_1292_, v_numArgs_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1299_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_object* v_00_u03b1_1300_, lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1301_ = stack[1].m_obj;
lean_object* v___y_1302_ = stack[2].m_obj;
lean_object* v___y_1303_ = stack[3].m_obj;
lean_object* v___y_1304_ = stack[4].m_obj;
lean_object* v___y_1305_ = stack[5].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(lean_box(0), v_msg_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0(v_00_u03b1_1309_, v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(lean_object* v_as_1317_, size_t v_sz_1318_, size_t v_i_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___redArg(v_as_1317_, v_sz_1318_, v_i_1319_, v_b_1320_);
return v___x_1326_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1317_ = stack[0].m_obj;
size_t v_sz_1318_ = stack[1].m_num;
size_t v_i_1319_ = stack[2].m_num;
lean_object* v_b_1320_ = stack[3].m_obj;
lean_object* v___y_1321_ = stack[4].m_obj;
lean_object* v___y_1322_ = stack[5].m_obj;
lean_object* v___y_1323_ = stack[6].m_obj;
lean_object* v___y_1324_ = stack[7].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1317_, v_sz_1318_, v_i_1319_, v_b_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1___boxed(lean_object* v_as_1328_, lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkHCongrWithArity_spec__1(v_as_1328_, v_sz_boxed_1337_, v_i_boxed_1338_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec_ref(v_as_1328_);
return v_res_1339_;
}
}
lean_object* l_Lean_Meta_mkHCongr(lean_object* v_f_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
lean_inc_ref(v_f_1340_);
v___x_1347_ = l_Lean_Meta_getFunInfo(v_f_1340_, v___x_1346_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = l_Lean_Meta_FunInfo_getArity(v_a_1348_);
lean_dec(v_a_1348_);
v___x_1350_ = l_Lean_Meta_mkHCongrWithArity(v_f_1340_, v___x_1349_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1350_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_f_1340_);
v_a_1351_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1347_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1340_ = stack[0].m_obj;
lean_object* v_a_1341_ = stack[1].m_obj;
lean_object* v_a_1342_ = stack[2].m_obj;
lean_object* v_a_1343_ = stack[3].m_obj;
lean_object* v_a_1344_ = stack[4].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Lean_Meta_mkHCongr(v_f_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongr___boxed(lean_object* v_f_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_mkHCongr(v_f_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1366_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(lean_object* v_a_1367_, lean_object* v_as_1368_, size_t v_i_1369_, size_t v_stop_1370_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_eq(v_i_1369_, v_stop_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_array_uget_borrowed(v_as_1368_, v_i_1369_);
v___x_1373_ = lean_nat_dec_eq(v_a_1367_, v___x_1372_);
if (v___x_1373_ == 0)
{
size_t v___x_1374_; size_t v___x_1375_; 
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1369_, v___x_1374_);
v_i_1369_ = v___x_1375_;
goto _start;
}
else
{
return v___x_1373_;
}
}
else
{
uint8_t v___x_1377_; 
v___x_1377_ = 0;
return v___x_1377_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1367_ = stack[0].m_obj;
lean_object* v_as_1368_ = stack[1].m_obj;
size_t v_i_1369_ = stack[2].m_num;
size_t v_stop_1370_ = stack[3].m_num;
uint8_t v_res_1378_;
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1367_, v_as_1368_, v_i_1369_, v_stop_1370_);
stack->m_num = v_res_1378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0___boxed(lean_object* v_a_1379_, lean_object* v_as_1380_, lean_object* v_i_1381_, lean_object* v_stop_1382_){
_start:
{
size_t v_i_boxed_1383_; size_t v_stop_boxed_1384_; uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_i_boxed_1383_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_stop_boxed_1384_ = lean_unbox_usize(v_stop_1382_);
lean_dec(v_stop_1382_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1379_, v_as_1380_, v_i_boxed_1383_, v_stop_boxed_1384_);
lean_dec_ref(v_as_1380_);
lean_dec(v_a_1379_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(lean_object* v_as_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_array_get_size(v_as_1387_);
v___x_1391_ = lean_nat_dec_lt(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
return v___x_1391_;
}
else
{
if (v___x_1391_ == 0)
{
return v___x_1391_;
}
else
{
size_t v___x_1392_; size_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = lean_usize_of_nat(v___x_1390_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_spec__0(v_a_1388_, v_as_1387_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1387_ = stack[0].m_obj;
lean_object* v_a_1388_ = stack[1].m_obj;
uint8_t v_res_1395_;
v_res_1395_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1387_, v_a_1388_);
stack->m_num = v_res_1395_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0___boxed(lean_object* v_as_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_as_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_as_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(lean_object* v_next_1400_, lean_object* v_upperBound_1401_, lean_object* v___x_1402_, lean_object* v_a_1403_, lean_object* v_b_1404_){
_start:
{
lean_object* v_a_1406_; uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_lt(v_a_1403_, v_upperBound_1401_);
if (v___x_1414_ == 0)
{
lean_dec(v_a_1403_);
return v_b_1404_;
}
else
{
lean_object* v___x_1415_; lean_object* v_backDeps_1416_; uint8_t v___x_1417_; 
v___x_1415_ = lean_array_fget_borrowed(v___x_1402_, v_a_1403_);
v_backDeps_1416_ = lean_ctor_get(v___x_1415_, 0);
v___x_1417_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_backDeps_1416_, v_next_1400_);
if (v___x_1417_ == 0)
{
v_a_1406_ = v_b_1404_;
goto v___jp_1405_;
}
else
{
uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = 0;
v___x_1419_ = lean_box(v___x_1418_);
v___x_1420_ = lean_array_get(v___x_1419_, v_b_1404_, v_a_1403_);
lean_dec(v___x_1419_);
v___x_1421_ = lean_unbox(v___x_1420_);
lean_dec(v___x_1420_);
switch(v___x_1421_)
{
case 2:
{
lean_dec(v_a_1403_);
goto v___jp_1410_;
}
case 0:
{
lean_dec(v_a_1403_);
goto v___jp_1410_;
}
default: 
{
v_a_1406_ = v_b_1404_;
goto v___jp_1405_;
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_a_1403_, v___x_1407_);
lean_dec(v_a_1403_);
v_a_1403_ = v___x_1408_;
v_b_1404_ = v_a_1406_;
goto _start;
}
v___jp_1410_:
{
uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = 0;
v___x_1412_ = lean_box(v___x_1411_);
v___x_1413_ = lean_array_set(v_b_1404_, v_next_1400_, v___x_1412_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg___boxed(lean_object* v_next_1422_, lean_object* v_upperBound_1423_, lean_object* v___x_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1422_, v_upperBound_1423_, v___x_1424_, v_a_1425_, v_b_1426_);
lean_dec_ref(v___x_1424_);
lean_dec(v_upperBound_1423_);
lean_dec(v_next_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(lean_object* v_upperBound_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_nat_dec_lt(v_a_1431_, v_upperBound_1428_);
if (v___x_1433_ == 0)
{
lean_dec(v_a_1431_);
return v_b_1432_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_a_1431_, v___x_1434_);
lean_inc(v___x_1435_);
v___x_1436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_a_1431_, v___x_1429_, v___x_1430_, v___x_1435_, v_b_1432_);
lean_dec(v_a_1431_);
v_a_1431_ = v___x_1435_;
v_b_1432_ = v___x_1436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg___boxed(lean_object* v_upperBound_1438_, lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1438_, v___x_1439_, v___x_1440_, v_a_1441_, v_b_1442_);
lean_dec_ref(v___x_1440_);
lean_dec(v___x_1439_);
lean_dec(v_upperBound_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(lean_object* v_info_1444_, lean_object* v_kinds_1445_){
_start:
{
lean_object* v_paramInfo_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_paramInfo_1446_ = lean_ctor_get(v_info_1444_, 0);
v___x_1447_ = lean_array_get_size(v_paramInfo_1446_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v___x_1447_, v___x_1447_, v_paramInfo_1446_, v___x_1448_, v_kinds_1445_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies___boxed(lean_object* v_info_1450_, lean_object* v_kinds_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_1450_, v_kinds_1451_);
lean_dec_ref(v_info_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(lean_object* v_next_1453_, lean_object* v_upperBound_1454_, lean_object* v___x_1455_, lean_object* v_inst_1456_, lean_object* v_R_1457_, lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v_c_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___redArg(v_next_1453_, v_upperBound_1454_, v___x_1455_, v_a_1458_, v_b_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1___boxed(lean_object* v_next_1462_, lean_object* v_upperBound_1463_, lean_object* v___x_1464_, lean_object* v_inst_1465_, lean_object* v_R_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v_c_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__1(v_next_1462_, v_upperBound_1463_, v___x_1464_, v_inst_1465_, v_R_1466_, v_a_1467_, v_b_1468_, v_c_1469_);
lean_dec_ref(v___x_1464_);
lean_dec(v_upperBound_1463_);
lean_dec(v_next_1462_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(lean_object* v_upperBound_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v_inst_1474_, lean_object* v_R_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_, lean_object* v_c_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___redArg(v_upperBound_1471_, v___x_1472_, v___x_1473_, v_a_1476_, v_b_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2___boxed(lean_object* v_upperBound_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_inst_1483_, lean_object* v_R_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v_c_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__2(v_upperBound_1480_, v___x_1481_, v___x_1482_, v_inst_1483_, v_R_1484_, v_a_1485_, v_b_1486_, v_c_1487_);
lean_dec_ref(v___x_1482_);
lean_dec(v___x_1481_);
lean_dec(v_upperBound_1480_);
return v_res_1488_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(lean_object* v_as_1489_, size_t v_i_1490_, size_t v_stop_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_eq(v_i_1490_, v_stop_1491_);
if (v___x_1492_ == 0)
{
uint8_t v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = 1;
v___x_1494_ = lean_array_uget_borrowed(v_as_1489_, v_i_1490_);
v___x_1495_ = lean_unbox(v___x_1494_);
switch(v___x_1495_)
{
case 3:
{
return v___x_1493_;
}
case 5:
{
return v___x_1493_;
}
default: 
{
size_t v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1490_, v___x_1496_);
v_i_1490_ = v___x_1497_;
goto _start;
}
}
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = 0;
return v___x_1499_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1489_ = stack[0].m_obj;
size_t v_i_1490_ = stack[1].m_num;
size_t v_stop_1491_ = stack[2].m_num;
uint8_t v_res_1500_;
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1489_, v_i_1490_, v_stop_1491_);
stack->m_num = v_res_1500_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0___boxed(lean_object* v_as_1501_, lean_object* v_i_1502_, lean_object* v_stop_1503_){
_start:
{
size_t v_i_boxed_1504_; size_t v_stop_boxed_1505_; uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_i_boxed_1504_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_stop_boxed_1505_ = lean_unbox_usize(v_stop_1503_);
lean_dec(v_stop_1503_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_as_1501_, v_i_boxed_1504_, v_stop_boxed_1505_);
lean_dec_ref(v_as_1501_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(lean_object* v_kinds_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get_size(v_kinds_1508_);
v___x_1511_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
return v___x_1511_;
}
else
{
if (v___x_1511_ == 0)
{
return v___x_1511_;
}
else
{
size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = ((size_t)0ULL);
v___x_1513_ = lean_usize_of_nat(v___x_1510_);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_spec__0(v_kinds_1508_, v___x_1512_, v___x_1513_);
return v___x_1514_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike_0interp(lean_interpreter_value* stack)
{
lean_object* v_kinds_1508_ = stack[0].m_obj;
uint8_t v_res_1515_;
v_res_1515_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1508_);
stack->m_num = v_res_1515_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike___boxed(lean_object* v_kinds_1516_){
_start:
{
uint8_t v_res_1517_; lean_object* v_r_1518_; 
v_res_1517_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_1516_);
lean_dec_ref(v_kinds_1516_);
v_r_1518_ = lean_box(v_res_1517_);
return v_r_1518_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(lean_object* v___x_1519_, lean_object* v_k_1520_, lean_object* v_xs_1521_, lean_object* v_type_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_array_get_borrowed(v___x_1519_, v_xs_1521_, v___x_1528_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc(v___x_1529_);
v___x_1530_ = lean_apply_7(v_k_1520_, v___x_1529_, v_type_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, lean_box(0));
return v___x_1530_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1519_ = stack[0].m_obj;
lean_object* v_k_1520_ = stack[1].m_obj;
lean_object* v_xs_1521_ = stack[2].m_obj;
lean_object* v_type_1522_ = stack[3].m_obj;
lean_object* v___y_1523_ = stack[4].m_obj;
lean_object* v___y_1524_ = stack[5].m_obj;
lean_object* v___y_1525_ = stack[6].m_obj;
lean_object* v___y_1526_ = stack[7].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1519_, v_k_1520_, v_xs_1521_, v_type_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed(lean_object* v___x_1532_, lean_object* v_k_1533_, lean_object* v_xs_1534_, lean_object* v_type_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0(v___x_1532_, v_k_1533_, v_xs_1534_, v_type_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_xs_1534_);
lean_dec_ref(v___x_1532_);
return v_res_1541_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(lean_object* v_type_1542_, lean_object* v_k_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1549_ = l_Lean_instInhabitedExpr;
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1550_, 0, v___x_1549_);
lean_closure_set(v___f_1550_, 1, v_k_1543_);
v___x_1551_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__4));
v___x_1552_ = 1;
v___x_1553_ = 0;
v___x_1554_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_type_1542_, v___x_1551_, v___f_1550_, v___x_1552_, v___x_1553_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1554_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1542_ = stack[0].m_obj;
lean_object* v_k_1543_ = stack[1].m_obj;
lean_object* v_a_1544_ = stack[2].m_obj;
lean_object* v_a_1545_ = stack[3].m_obj;
lean_object* v_a_1546_ = stack[4].m_obj;
lean_object* v_a_1547_ = stack[5].m_obj;
lean_object* v_res_1555_;
v_res_1555_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1542_, v_k_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
stack->m_obj
 = v_res_1555_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg___boxed(lean_object* v_type_1556_, lean_object* v_k_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1556_, v_k_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
return v_res_1563_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_object* v_00_u03b1_1564_, lean_object* v_type_1565_, lean_object* v_k_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_1565_, v_k_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1565_ = stack[1].m_obj;
lean_object* v_k_1566_ = stack[2].m_obj;
lean_object* v_a_1567_ = stack[3].m_obj;
lean_object* v_a_1568_ = stack[4].m_obj;
lean_object* v_a_1569_ = stack[5].m_obj;
lean_object* v_a_1570_ = stack[6].m_obj;
lean_object* v_res_1573_;
v_res_1573_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(lean_box(0), v_type_1565_, v_k_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
stack->m_obj
 = v_res_1573_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___boxed(lean_object* v_00_u03b1_1574_, lean_object* v_type_1575_, lean_object* v_k_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext(v_00_u03b1_1574_, v_type_1575_, v_k_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(lean_object* v_kinds_1586_, uint8_t v___x_1587_, lean_object* v_as_1588_, size_t v_sz_1589_, size_t v_i_1590_, lean_object* v_b_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_usize_dec_lt(v_i_1590_, v_sz_1589_);
if (v___x_1592_ == 0)
{
lean_inc_ref(v_b_1591_);
return v_b_1591_;
}
else
{
uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1593_ = 0;
v___x_1594_ = lean_box(0);
v_a_1595_ = lean_array_uget_borrowed(v_as_1588_, v_i_1590_);
v___x_1596_ = lean_box(v___x_1593_);
v___x_1597_ = lean_array_get(v___x_1596_, v_kinds_1586_, v_a_1595_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_unbox(v___x_1597_);
lean_dec(v___x_1597_);
if (v___x_1598_ == 2)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_box(v___x_1587_);
v___x_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1594_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; 
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1590_, v___x_1603_);
v_i_1590_ = v___x_1604_;
v_b_1591_ = v___x_1602_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kinds_1586_ = stack[0].m_obj;
uint8_t v___x_1587_ = stack[1].m_num;
lean_object* v_as_1588_ = stack[2].m_obj;
size_t v_sz_1589_ = stack[3].m_num;
size_t v_i_1590_ = stack[4].m_num;
lean_object* v_b_1591_ = stack[5].m_obj;
lean_object* v_res_1606_;
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1586_, v___x_1587_, v_as_1588_, v_sz_1589_, v_i_1590_, v_b_1591_);
stack->m_obj
 = v_res_1606_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___boxed(lean_object* v_kinds_1607_, lean_object* v___x_1608_, lean_object* v_as_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_b_1612_){
_start:
{
uint8_t v___x_569__boxed_1613_; size_t v_sz_boxed_1614_; size_t v_i_boxed_1615_; lean_object* v_res_1616_; 
v___x_569__boxed_1613_ = lean_unbox(v___x_1608_);
v_sz_boxed_1614_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1615_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1607_, v___x_569__boxed_1613_, v_as_1609_, v_sz_boxed_1614_, v_i_boxed_1615_, v_b_1612_);
lean_dec_ref(v_b_1612_);
lean_dec_ref(v_as_1609_);
lean_dec_ref(v_kinds_1607_);
return v_res_1616_;
}
}
uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(lean_object* v_info_1617_, lean_object* v_kinds_1618_, lean_object* v_i_1619_){
_start:
{
lean_object* v_paramInfo_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v_isDecInst_1623_; 
v_paramInfo_1620_ = lean_ctor_get(v_info_1617_, 0);
v___x_1621_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_1622_ = lean_array_get_borrowed(v___x_1621_, v_paramInfo_1620_, v_i_1619_);
v_isDecInst_1623_ = lean_ctor_get_uint8(v___x_1622_, sizeof(void*)*1 + 3);
if (v_isDecInst_1623_ == 0)
{
return v_isDecInst_1623_;
}
else
{
lean_object* v_backDeps_1624_; lean_object* v___x_1625_; size_t v_sz_1626_; size_t v___x_1627_; lean_object* v___x_1628_; lean_object* v_fst_1629_; 
v_backDeps_1624_ = lean_ctor_get(v___x_1622_, 0);
v___x_1625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0___closed__0));
v_sz_1626_ = lean_array_size(v_backDeps_1624_);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_spec__0(v_kinds_1618_, v_isDecInst_1623_, v_backDeps_1624_, v_sz_1626_, v___x_1627_, v___x_1625_);
v_fst_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_fst_1629_);
lean_dec_ref(v___x_1628_);
if (lean_obj_tag(v_fst_1629_) == 0)
{
uint8_t v___x_1630_; 
v___x_1630_ = 0;
return v___x_1630_;
}
else
{
lean_object* v_val_1631_; uint8_t v___x_1632_; 
v_val_1631_ = lean_ctor_get(v_fst_1629_, 0);
lean_inc(v_val_1631_);
lean_dec_ref_known(v_fst_1629_, 1);
v___x_1632_ = lean_unbox(v_val_1631_);
lean_dec(v_val_1631_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1617_ = stack[0].m_obj;
lean_object* v_kinds_1618_ = stack[1].m_obj;
lean_object* v_i_1619_ = stack[2].m_obj;
uint8_t v_res_1633_;
v_res_1633_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1617_, v_kinds_1618_, v_i_1619_);
stack->m_num = v_res_1633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst___boxed(lean_object* v_info_1634_, lean_object* v_kinds_1635_, lean_object* v_i_1636_){
_start:
{
uint8_t v_res_1637_; lean_object* v_r_1638_; 
v_res_1637_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_1634_, v_kinds_1635_, v_i_1636_);
lean_dec(v_i_1636_);
lean_dec_ref(v_kinds_1635_);
lean_dec_ref(v_info_1634_);
v_r_1638_ = lean_box(v_res_1637_);
return v_r_1638_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(lean_object* v_type_1639_, lean_object* v_k_1640_, uint8_t v_cleanupAnnotations_1641_, uint8_t v_whnfType_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___f_1648_; lean_object* v___x_1649_; 
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1648_, 0, v_k_1640_);
v___x_1649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1639_, v___f_1648_, v_cleanupAnnotations_1641_, v_whnfType_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1649_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1649_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1639_ = stack[0].m_obj;
lean_object* v_k_1640_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1641_ = stack[2].m_num;
uint8_t v_whnfType_1642_ = stack[3].m_num;
lean_object* v___y_1643_ = stack[4].m_obj;
lean_object* v___y_1644_ = stack[5].m_obj;
lean_object* v___y_1645_ = stack[6].m_obj;
lean_object* v___y_1646_ = stack[7].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1639_, v_k_1640_, v_cleanupAnnotations_1641_, v_whnfType_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg___boxed(lean_object* v_type_1667_, lean_object* v_k_1668_, lean_object* v_cleanupAnnotations_1669_, lean_object* v_whnfType_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1676_; uint8_t v_whnfType_boxed_1677_; lean_object* v_res_1678_; 
v_cleanupAnnotations_boxed_1676_ = lean_unbox(v_cleanupAnnotations_1669_);
v_whnfType_boxed_1677_ = lean_unbox(v_whnfType_1670_);
v_res_1678_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1667_, v_k_1668_, v_cleanupAnnotations_boxed_1676_, v_whnfType_boxed_1677_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1678_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_object* v_00_u03b1_1679_, lean_object* v_type_1680_, lean_object* v_k_1681_, uint8_t v_cleanupAnnotations_1682_, uint8_t v_whnfType_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_1680_, v_k_1681_, v_cleanupAnnotations_1682_, v_whnfType_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1680_ = stack[1].m_obj;
lean_object* v_k_1681_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1682_ = stack[3].m_num;
uint8_t v_whnfType_1683_ = stack[4].m_num;
lean_object* v___y_1684_ = stack[5].m_obj;
lean_object* v___y_1685_ = stack[6].m_obj;
lean_object* v___y_1686_ = stack[7].m_obj;
lean_object* v___y_1687_ = stack[8].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(lean_box(0), v_type_1680_, v_k_1681_, v_cleanupAnnotations_1682_, v_whnfType_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_type_1692_, lean_object* v_k_1693_, lean_object* v_cleanupAnnotations_1694_, lean_object* v_whnfType_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1701_; uint8_t v_whnfType_boxed_1702_; lean_object* v_res_1703_; 
v_cleanupAnnotations_boxed_1701_ = lean_unbox(v_cleanupAnnotations_1694_);
v_whnfType_boxed_1702_ = lean_unbox(v_whnfType_1695_);
v_res_1703_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2(v_00_u03b1_1691_, v_type_1692_, v_k_1693_, v_cleanupAnnotations_boxed_1701_, v_whnfType_boxed_1702_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1703_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(lean_object* v_upperBound_1704_, lean_object* v_val_1705_, lean_object* v_xs_1706_, lean_object* v___x_1707_, lean_object* v___x_1708_, uint8_t v___x_1709_, lean_object* v_a_1710_, lean_object* v_b_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_a_1717_; uint8_t v___x_1721_; 
v___x_1721_ = lean_nat_dec_lt(v_a_1710_, v_upperBound_1704_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_a_1710_);
lean_dec(v___x_1708_);
lean_dec_ref(v___x_1707_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1711_);
return v___x_1722_;
}
else
{
lean_object* v_numParams_1723_; uint8_t v___x_1724_; 
v_numParams_1723_ = lean_ctor_get(v_val_1705_, 3);
v___x_1724_ = lean_nat_dec_lt(v_a_1710_, v_numParams_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_array_fget_borrowed(v_xs_1706_, v_a_1710_);
v___x_1726_ = l_Lean_Expr_fvarId_x21(v___x_1725_);
v___x_1727_ = l_Lean_FVarId_getDecl___redArg(v___x_1726_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; uint8_t v___y_1730_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1733_ = l_Lean_LocalDecl_userName(v_a_1728_);
lean_dec(v_a_1728_);
lean_inc(v___x_1708_);
lean_inc_ref(v___x_1707_);
v___x_1734_ = l_Lean_isSubobjectField_x3f(v___x_1707_, v___x_1708_, v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
v___y_1730_ = v___x_1724_;
goto v___jp_1729_;
}
else
{
lean_dec_ref_known(v___x_1734_, 1);
v___y_1730_ = v___x_1709_;
goto v___jp_1729_;
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(v___y_1730_);
v___x_1732_ = lean_array_push(v_b_1711_, v___x_1731_);
v_a_1717_ = v___x_1732_;
goto v___jp_1716_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_b_1711_);
lean_dec(v_a_1710_);
lean_dec(v___x_1708_);
lean_dec_ref(v___x_1707_);
v_a_1735_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1727_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1727_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = 0;
v___x_1744_ = lean_box(v___x_1743_);
v___x_1745_ = lean_array_push(v_b_1711_, v___x_1744_);
v_a_1717_ = v___x_1745_;
goto v___jp_1716_;
}
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_add(v_a_1710_, v___x_1718_);
lean_dec(v_a_1710_);
v_a_1710_ = v___x_1719_;
v_b_1711_ = v_a_1717_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1704_ = stack[0].m_obj;
lean_object* v_val_1705_ = stack[1].m_obj;
lean_object* v_xs_1706_ = stack[2].m_obj;
lean_object* v___x_1707_ = stack[3].m_obj;
lean_object* v___x_1708_ = stack[4].m_obj;
uint8_t v___x_1709_ = stack[5].m_num;
lean_object* v_a_1710_ = stack[6].m_obj;
lean_object* v_b_1711_ = stack[7].m_obj;
lean_object* v___y_1712_ = stack[8].m_obj;
lean_object* v___y_1713_ = stack[9].m_obj;
lean_object* v___y_1714_ = stack[10].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1704_, v_val_1705_, v_xs_1706_, v___x_1707_, v___x_1708_, v___x_1709_, v_a_1710_, v_b_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_1747_, lean_object* v_val_1748_, lean_object* v_xs_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v_a_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_5306__boxed_1759_; lean_object* v_res_1760_; 
v___x_5306__boxed_1759_ = lean_unbox(v___x_1752_);
v_res_1760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_1747_, v_val_1748_, v_xs_1749_, v___x_1750_, v___x_1751_, v___x_5306__boxed_1759_, v_a_1753_, v_b_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v_xs_1749_);
lean_dec_ref(v_val_1748_);
lean_dec(v_upperBound_1747_);
return v_res_1760_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(lean_object* v_val_1763_, lean_object* v_induct_1764_, uint8_t v___x_1765_, lean_object* v_xs_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v_env_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1773_ = lean_st_ref_get(v___y_1771_);
v_env_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc_ref(v_env_1774_);
lean_dec(v___x_1773_);
v___x_1775_ = lean_array_get_size(v_xs_1766_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___closed__0));
v___x_1778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v___x_1775_, v_val_1763_, v_xs_1766_, v_env_1774_, v_induct_1764_, v___x_1765_, v___x_1776_, v___x_1777_, v___y_1768_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1787_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1787_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1779_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1788_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1778_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1763_ = stack[0].m_obj;
lean_object* v_induct_1764_ = stack[1].m_obj;
uint8_t v___x_1765_ = stack[2].m_num;
lean_object* v_xs_1766_ = stack[3].m_obj;
lean_object* v_x_1767_ = stack[4].m_obj;
lean_object* v___y_1768_ = stack[5].m_obj;
lean_object* v___y_1769_ = stack[6].m_obj;
lean_object* v___y_1770_ = stack[7].m_obj;
lean_object* v___y_1771_ = stack[8].m_obj;
lean_object* v_res_1796_;
v_res_1796_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1763_, v_induct_1764_, v___x_1765_, v_xs_1766_, v_x_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
stack->m_obj
 = v_res_1796_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed(lean_object* v_val_1797_, lean_object* v_induct_1798_, lean_object* v___x_1799_, lean_object* v_xs_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v___x_5440__boxed_1807_; lean_object* v_res_1808_; 
v___x_5440__boxed_1807_ = lean_unbox(v___x_1799_);
v_res_1808_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0(v_val_1797_, v_induct_1798_, v___x_5440__boxed_1807_, v_xs_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_x_1801_);
lean_dec_ref(v_xs_1800_);
lean_dec_ref(v_val_1797_);
return v_res_1808_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
lean_ctor_set(v___x_1815_, 2, v___x_1814_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
lean_ctor_set(v___x_1815_, 4, v___x_1813_);
lean_ctor_set(v___x_1815_, 5, v___x_1813_);
lean_ctor_set(v___x_1815_, 6, v___x_1813_);
lean_ctor_set(v___x_1815_, 7, v___x_1813_);
lean_ctor_set(v___x_1815_, 8, v___x_1813_);
lean_ctor_set(v___x_1815_, 9, v___x_1813_);
lean_ctor_set(v___x_1815_, 10, v___x_1813_);
lean_ctor_set(v___x_1815_, 11, v___x_1812_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(32u);
v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = ((size_t)5ULL);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_unsigned_to_nat(32u);
v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1824_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
lean_ctor_set(v___x_1824_, 2, v___x_1820_);
lean_ctor_set(v___x_1824_, 3, v___x_1820_);
lean_ctor_set_usize(v___x_1824_, 4, v___x_1819_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_box(1);
v___x_1826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1825_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1862_, lean_object* v_declHint_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_env_1868_; uint8_t v___x_1869_; 
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_st_ref_get(v___y_1864_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1868_);
lean_dec(v___x_1867_);
v___x_1869_ = l_Lean_Name_isAnonymous(v_declHint_1863_);
if (v___x_1869_ == 0)
{
uint8_t v_isExporting_1870_; 
v_isExporting_1870_ = lean_ctor_get_uint8(v_env_1868_, sizeof(void*)*13);
if (v_isExporting_1870_ == 0)
{
lean_object* v___x_1871_; 
lean_dec_ref(v_env_1868_);
lean_dec(v_declHint_1863_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_msg_1862_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
lean_inc_ref(v_env_1868_);
v___x_1872_ = l_Lean_Environment_setExporting(v_env_1868_, v___x_1869_);
lean_inc(v_declHint_1863_);
lean_inc_ref(v___x_1872_);
v___x_1873_ = l_Lean_Environment_contains(v___x_1872_, v_declHint_1863_, v_isExporting_1870_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_dec_ref(v___x_1872_);
lean_dec_ref(v_env_1868_);
lean_dec(v_declHint_1863_);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_msg_1862_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v_c_1880_; lean_object* v___x_1881_; 
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1877_ = l_Lean_Options_empty;
v___x_1878_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1872_);
lean_ctor_set(v___x_1878_, 1, v___x_1875_);
lean_ctor_set(v___x_1878_, 2, v___x_1876_);
lean_ctor_set(v___x_1878_, 3, v___x_1877_);
lean_inc(v_declHint_1863_);
v___x_1879_ = l_Lean_MessageData_ofConstName(v_declHint_1863_, v___x_1869_);
v_c_1880_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1880_, 0, v___x_1878_);
lean_ctor_set(v_c_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1868_, v_declHint_1863_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v_env_1868_);
lean_dec(v_declHint_1863_);
v___x_1882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_c_1880_);
v___x_1884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_MessageData_note(v___x_1885_);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v_msg_1862_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
else
{
lean_object* v_val_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1945_; 
v_val_1889_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1891_ = v___x_1881_;
v_isShared_1892_ = v_isSharedCheck_1945_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_val_1889_);
lean_dec(v___x_1881_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1945_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_modules_1894_; lean_object* v_moduleNames_1895_; lean_object* v_mod_1896_; uint8_t v___y_1898_; uint8_t v___x_1928_; 
v___x_1893_ = l_Lean_Environment_header(v_env_1868_);
lean_dec_ref(v_env_1868_);
v_modules_1894_ = lean_ctor_get(v___x_1893_, 3);
lean_inc_ref(v_modules_1894_);
v_moduleNames_1895_ = lean_ctor_get(v___x_1893_, 4);
lean_inc_ref(v_moduleNames_1895_);
lean_dec_ref(v___x_1893_);
v_mod_1896_ = lean_array_get(v___x_1866_, v_moduleNames_1895_, v_val_1889_);
lean_dec_ref(v_moduleNames_1895_);
v___x_1928_ = l_Lean_isPrivateName(v_declHint_1863_);
lean_dec(v_declHint_1863_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = lean_array_get_size(v_modules_1894_);
v___x_1930_ = lean_nat_dec_lt(v_val_1889_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v_modules_1894_);
lean_dec(v_val_1889_);
v___y_1898_ = v___x_1928_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1931_; lean_object* v_toImport_1932_; uint8_t v_isExported_1933_; 
v___x_1931_ = lean_array_fget(v_modules_1894_, v_val_1889_);
lean_dec(v_val_1889_);
lean_dec_ref(v_modules_1894_);
v_toImport_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_ref(v_toImport_1932_);
lean_dec(v___x_1931_);
v_isExported_1933_ = lean_ctor_get_uint8(v_toImport_1932_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1932_);
v___y_1898_ = v_isExported_1933_;
goto v___jp_1897_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_modules_1894_);
lean_del_object(v___x_1891_);
lean_dec(v_val_1889_);
v___x_1934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_c_1880_);
v___x_1936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_MessageData_ofName(v_mod_1896_);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = l_Lean_MessageData_note(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_msg_1862_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
v___jp_1897_:
{
if (v___y_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v_c_1880_);
v___x_1901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_MessageData_ofName(v_mod_1896_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Lean_MessageData_note(v___x_1906_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_msg_1862_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1908_);
v___x_1910_ = v___x_1891_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v_c_1880_);
v___x_1914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_MessageData_ofName(v_mod_1896_);
lean_inc_ref(v___x_1916_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1916_);
v___x_1921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_MessageData_note(v___x_1922_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_msg_1862_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1924_);
v___x_1926_ = v___x_1891_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
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
lean_object* v___x_1946_; 
lean_dec_ref(v_env_1868_);
lean_dec(v_declHint_1863_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_msg_1862_);
return v___x_1946_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1862_ = stack[0].m_obj;
lean_object* v_declHint_1863_ = stack[1].m_obj;
lean_object* v___y_1864_ = stack[2].m_obj;
lean_object* v_res_1947_;
v_res_1947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1862_, v_declHint_1863_, v___y_1864_);
stack->m_obj
 = v_res_1947_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1948_, v_declHint_1949_, v___y_1950_);
lean_dec(v___y_1950_);
return v_res_1952_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msg_1953_, lean_object* v_declHint_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1970_; 
v___x_1960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1953_, v_declHint_1954_, v___y_1958_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1970_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1970_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1965_ = l_Lean_unknownIdentifierMessageTag;
v___x_1966_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v_a_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1953_ = stack[0].m_obj;
lean_object* v_declHint_1954_ = stack[1].m_obj;
lean_object* v___y_1955_ = stack[2].m_obj;
lean_object* v___y_1956_ = stack[3].m_obj;
lean_object* v___y_1957_ = stack[4].m_obj;
lean_object* v___y_1958_ = stack[5].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1953_, v_declHint_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1972_, lean_object* v_declHint_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_1972_, v_declHint_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1980_, lean_object* v_msg_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_toCold_1987_; lean_object* v_currRecDepth_1988_; lean_object* v_ref_1989_; uint16_t v_optionFlags_1990_; uint8_t v_suppressElabErrors_1991_; uint8_t v_isRecordingDeps_1992_; lean_object* v_ref_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_toCold_1987_ = lean_ctor_get(v___y_1984_, 0);
v_currRecDepth_1988_ = lean_ctor_get(v___y_1984_, 1);
v_ref_1989_ = lean_ctor_get(v___y_1984_, 2);
v_optionFlags_1990_ = lean_ctor_get_uint16(v___y_1984_, sizeof(void*)*3);
v_suppressElabErrors_1991_ = lean_ctor_get_uint8(v___y_1984_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1992_ = lean_ctor_get_uint8(v___y_1984_, sizeof(void*)*3 + 3);
v_ref_1993_ = l_Lean_replaceRef(v_ref_1980_, v_ref_1989_);
lean_inc(v_currRecDepth_1988_);
lean_inc_ref(v_toCold_1987_);
v___x_1994_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1994_, 0, v_toCold_1987_);
lean_ctor_set(v___x_1994_, 1, v_currRecDepth_1988_);
lean_ctor_set(v___x_1994_, 2, v_ref_1993_);
lean_ctor_set_uint16(v___x_1994_, sizeof(void*)*3, v_optionFlags_1990_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*3 + 2, v_suppressElabErrors_1991_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*3 + 3, v_isRecordingDeps_1992_);
v___x_1995_ = l_Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0___redArg(v_msg_1981_, v___y_1982_, v___y_1983_, v___x_1994_, v___y_1985_);
lean_dec_ref_known(v___x_1994_, 3);
return v___x_1995_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1980_ = stack[0].m_obj;
lean_object* v_msg_1981_ = stack[1].m_obj;
lean_object* v___y_1982_ = stack[2].m_obj;
lean_object* v___y_1983_ = stack[3].m_obj;
lean_object* v___y_1984_ = stack[4].m_obj;
lean_object* v___y_1985_ = stack[5].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1980_, v_msg_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
stack->m_obj
 = v_res_1996_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1997_, lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1997_, v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v_ref_1997_);
return v_res_2004_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_2005_, lean_object* v_msg_2006_, lean_object* v_declHint_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_a_2014_; lean_object* v___x_2015_; 
v___x_2013_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_2006_, v_declHint_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2005_, v_a_2014_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2015_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2005_ = stack[0].m_obj;
lean_object* v_msg_2006_ = stack[1].m_obj;
lean_object* v_declHint_2007_ = stack[2].m_obj;
lean_object* v___y_2008_ = stack[3].m_obj;
lean_object* v___y_2009_ = stack[4].m_obj;
lean_object* v___y_2010_ = stack[5].m_obj;
lean_object* v___y_2011_ = stack[6].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2005_, v_msg_2006_, v_declHint_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2017_, lean_object* v_msg_2018_, lean_object* v_declHint_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2017_, v_msg_2018_, v_declHint_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_ref_2017_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_2032_, lean_object* v_constName_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2039_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_2040_ = 0;
lean_inc(v_constName_2033_);
v___x_2041_ = l_Lean_MessageData_ofConstName(v_constName_2033_, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2039_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2032_, v___x_2044_, v_constName_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2045_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2032_ = stack[0].m_obj;
lean_object* v_constName_2033_ = stack[1].m_obj;
lean_object* v___y_2034_ = stack[2].m_obj;
lean_object* v___y_2035_ = stack[3].m_obj;
lean_object* v___y_2036_ = stack[4].m_obj;
lean_object* v___y_2037_ = stack[5].m_obj;
lean_object* v_res_2046_;
v_res_2046_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2032_, v_constName_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_2047_, lean_object* v_constName_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2047_, v_constName_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v_ref_2047_);
return v_res_2054_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(lean_object* v_constName_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_ref_2061_; lean_object* v___x_2062_; 
v_ref_2061_ = lean_ctor_get(v___y_2058_, 2);
v___x_2062_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2061_, v_constName_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2062_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2055_ = stack[0].m_obj;
lean_object* v___y_2056_ = stack[1].m_obj;
lean_object* v___y_2057_ = stack[2].m_obj;
lean_object* v___y_2058_ = stack[3].m_obj;
lean_object* v___y_2059_ = stack[4].m_obj;
lean_object* v_res_2063_;
v_res_2063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
stack->m_obj
 = v_res_2063_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2070_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_env_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_st_ref_get(v___y_2075_);
v_env_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_ref(v_env_2078_);
lean_dec(v___x_2077_);
v___x_2079_ = 0;
lean_inc(v_constName_2071_);
v___x_2080_ = l_Lean_Environment_find_x3f(v_env_2078_, v_constName_2071_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2081_;
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_constName_2071_);
v_val_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_val_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 0);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2071_ = stack[0].m_obj;
lean_object* v___y_2072_ = stack[1].m_obj;
lean_object* v___y_2073_ = stack[2].m_obj;
lean_object* v___y_2074_ = stack[3].m_obj;
lean_object* v___y_2075_ = stack[4].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0___boxed(lean_object* v_constName_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_constName_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2097_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(lean_object* v_f_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
if (lean_obj_tag(v_f_2098_) == 4)
{
lean_object* v_declName_2104_; lean_object* v___x_2105_; 
v_declName_2104_ = lean_ctor_get(v_f_2098_, 0);
lean_inc(v_declName_2104_);
lean_dec_ref_known(v_f_2098_, 2);
v___x_2105_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_declName_2104_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2129_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2129_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2129_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
if (lean_obj_tag(v_a_2106_) == 6)
{
lean_object* v_val_2110_; lean_object* v___x_2111_; lean_object* v_env_2112_; lean_object* v_toConstantVal_2113_; lean_object* v_induct_2114_; uint8_t v___x_2115_; 
v_val_2110_ = lean_ctor_get(v_a_2106_, 0);
lean_inc_ref(v_val_2110_);
lean_dec_ref_known(v_a_2106_, 1);
v___x_2111_ = lean_st_ref_get(v_a_2102_);
v_env_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2112_);
lean_dec(v___x_2111_);
v_toConstantVal_2113_ = lean_ctor_get(v_val_2110_, 0);
v_induct_2114_ = lean_ctor_get(v_val_2110_, 1);
lean_inc(v_induct_2114_);
v___x_2115_ = l_Lean_isClass(v_env_2112_, v_induct_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_induct_2114_);
lean_dec_ref(v_val_2110_);
v___x_2116_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2116_);
v___x_2118_ = v___x_2108_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v_type_2120_; lean_object* v___x_2121_; lean_object* v___f_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2108_);
v_type_2120_ = lean_ctor_get(v_toConstantVal_2113_, 2);
lean_inc_ref(v_type_2120_);
v___x_2121_ = lean_box(v___x_2115_);
v___f_2122_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2122_, 0, v_val_2110_);
lean_closure_set(v___f_2122_, 1, v_induct_2114_);
lean_closure_set(v___f_2122_, 2, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__2___redArg(v_type_2120_, v___f_2122_, v___x_2115_, v___x_2123_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2124_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_a_2106_);
v___x_2125_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2125_);
v___x_2127_ = v___x_2108_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2105_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2105_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v_f_2098_);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2098_ = stack[0].m_obj;
lean_object* v_a_2099_ = stack[1].m_obj;
lean_object* v_a_2100_ = stack[2].m_obj;
lean_object* v_a_2101_ = stack[3].m_obj;
lean_object* v_a_2102_ = stack[4].m_obj;
lean_object* v_res_2140_;
v_res_2140_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
stack->m_obj
 = v_res_2140_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f___boxed(lean_object* v_f_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
return v_res_2147_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(lean_object* v_upperBound_2148_, lean_object* v_val_2149_, lean_object* v_xs_2150_, lean_object* v___x_2151_, lean_object* v___x_2152_, uint8_t v___x_2153_, lean_object* v_inst_2154_, lean_object* v_R_2155_, lean_object* v_a_2156_, lean_object* v_b_2157_, lean_object* v_c_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___redArg(v_upperBound_2148_, v_val_2149_, v_xs_2150_, v___x_2151_, v___x_2152_, v___x_2153_, v_a_2156_, v_b_2157_, v___y_2159_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2148_ = stack[0].m_obj;
lean_object* v_val_2149_ = stack[1].m_obj;
lean_object* v_xs_2150_ = stack[2].m_obj;
lean_object* v___x_2151_ = stack[3].m_obj;
lean_object* v___x_2152_ = stack[4].m_obj;
uint8_t v___x_2153_ = stack[5].m_num;
lean_object* v_a_2156_ = stack[8].m_obj;
lean_object* v_b_2157_ = stack[9].m_obj;
lean_object* v___y_2159_ = stack[11].m_obj;
lean_object* v___y_2160_ = stack[12].m_obj;
lean_object* v___y_2161_ = stack[13].m_obj;
lean_object* v___y_2162_ = stack[14].m_obj;
lean_object* v_res_2165_;
v_res_2165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2148_, v_val_2149_, v_xs_2150_, v___x_2151_, v___x_2152_, v___x_2153_, lean_box(0), lean_box(0), v_a_2156_, v_b_2157_, lean_box(0), v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
stack->m_obj
 = v_res_2165_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1___boxed(lean_object* v_upperBound_2166_, lean_object* v_val_2167_, lean_object* v_xs_2168_, lean_object* v___x_2169_, lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_inst_2172_, lean_object* v_R_2173_, lean_object* v_a_2174_, lean_object* v_b_2175_, lean_object* v_c_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v___x_6403__boxed_2182_; lean_object* v_res_2183_; 
v___x_6403__boxed_2182_ = lean_unbox(v___x_2171_);
v_res_2183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__1(v_upperBound_2166_, v_val_2167_, v_xs_2168_, v___x_2169_, v___x_2170_, v___x_6403__boxed_2182_, v_inst_2172_, v_R_2173_, v_a_2174_, v_b_2175_, v_c_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec_ref(v_xs_2168_);
lean_dec_ref(v_val_2167_);
lean_dec(v_upperBound_2166_);
return v_res_2183_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_object* v_00_u03b1_2184_, lean_object* v_constName_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___redArg(v_constName_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2185_ = stack[1].m_obj;
lean_object* v___y_2186_ = stack[2].m_obj;
lean_object* v___y_2187_ = stack[3].m_obj;
lean_object* v___y_2188_ = stack[4].m_obj;
lean_object* v___y_2189_ = stack[5].m_obj;
lean_object* v_res_2192_;
v_res_2192_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(lean_box(0), v_constName_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
stack->m_obj
 = v_res_2192_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_constName_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0(v_00_u03b1_2193_, v_constName_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2200_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2201_, lean_object* v_ref_2202_, lean_object* v_constName_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg(v_ref_2202_, v_constName_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2202_ = stack[1].m_obj;
lean_object* v_constName_2203_ = stack[2].m_obj;
lean_object* v___y_2204_ = stack[3].m_obj;
lean_object* v___y_2205_ = stack[4].m_obj;
lean_object* v___y_2206_ = stack[5].m_obj;
lean_object* v___y_2207_ = stack[6].m_obj;
lean_object* v_res_2210_;
v_res_2210_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(lean_box(0), v_ref_2202_, v_constName_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
stack->m_obj
 = v_res_2210_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2211_, lean_object* v_ref_2212_, lean_object* v_constName_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2(v_00_u03b1_2211_, v_ref_2212_, v_constName_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v_ref_2212_);
return v_res_2219_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_2220_, lean_object* v_ref_2221_, lean_object* v_msg_2222_, lean_object* v_declHint_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_2221_, v_msg_2222_, v_declHint_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2221_ = stack[1].m_obj;
lean_object* v_msg_2222_ = stack[2].m_obj;
lean_object* v_declHint_2223_ = stack[3].m_obj;
lean_object* v___y_2224_ = stack[4].m_obj;
lean_object* v___y_2225_ = stack[5].m_obj;
lean_object* v___y_2226_ = stack[6].m_obj;
lean_object* v___y_2227_ = stack[7].m_obj;
lean_object* v_res_2230_;
v_res_2230_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_ref_2221_, v_msg_2222_, v_declHint_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
stack->m_obj
 = v_res_2230_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_ref_2232_, lean_object* v_msg_2233_, lean_object* v_declHint_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_2231_, v_ref_2232_, v_msg_2233_, v_declHint_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v_ref_2232_);
return v_res_2240_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_2241_, lean_object* v_declHint_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_2241_, v_declHint_2242_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2241_ = stack[0].m_obj;
lean_object* v_declHint_2242_ = stack[1].m_obj;
lean_object* v___y_2243_ = stack[2].m_obj;
lean_object* v___y_2244_ = stack[3].m_obj;
lean_object* v___y_2245_ = stack[4].m_obj;
lean_object* v___y_2246_ = stack[5].m_obj;
lean_object* v_res_2249_;
v_res_2249_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2241_, v_declHint_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
stack->m_obj
 = v_res_2249_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2250_, lean_object* v_declHint_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6(v_msg_2250_, v_declHint_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2257_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2258_, lean_object* v_ref_2259_, lean_object* v_msg_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_2259_, v_msg_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2259_ = stack[1].m_obj;
lean_object* v_msg_2260_ = stack[2].m_obj;
lean_object* v___y_2261_ = stack[3].m_obj;
lean_object* v___y_2262_ = stack[4].m_obj;
lean_object* v___y_2263_ = stack[5].m_obj;
lean_object* v___y_2264_ = stack[6].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(lean_box(0), v_ref_2259_, v_msg_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_ref_2269_, lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_2268_, v_ref_2269_, v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_ref_2269_);
return v_res_2276_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(lean_object* v_info_2277_, lean_object* v_a_2278_, lean_object* v_____r_2279_, lean_object* v_result_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2277_, v_result_2280_, v_a_2278_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2287_ = 0;
v___x_2288_ = lean_box(v___x_2287_);
v___x_2289_ = lean_array_push(v_result_2280_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
else
{
uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2292_ = 5;
v___x_2293_ = lean_box(v___x_2292_);
v___x_2294_ = lean_array_push(v_result_2280_, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2277_ = stack[0].m_obj;
lean_object* v_a_2278_ = stack[1].m_obj;
lean_object* v_____r_2279_ = stack[2].m_obj;
lean_object* v_result_2280_ = stack[3].m_obj;
lean_object* v___y_2281_ = stack[4].m_obj;
lean_object* v___y_2282_ = stack[5].m_obj;
lean_object* v___y_2283_ = stack[6].m_obj;
lean_object* v___y_2284_ = stack[7].m_obj;
lean_object* v_res_2297_;
v_res_2297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2277_, v_a_2278_, v_____r_2279_, v_result_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
stack->m_obj
 = v_res_2297_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0___boxed(lean_object* v_info_2298_, lean_object* v_a_2299_, lean_object* v_____r_2300_, lean_object* v_result_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2298_, v_a_2299_, v_____r_2300_, v_result_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v_a_2299_);
lean_dec_ref(v_info_2298_);
return v_res_2307_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(lean_object* v_info_2308_, lean_object* v_upperBound_2309_, lean_object* v___x_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_a_2320_; lean_object* v___y_2325_; uint8_t v___x_2344_; 
v___x_2344_ = lean_nat_dec_lt(v_a_2312_, v_upperBound_2309_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_a_2312_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_b_2313_);
return v___x_2345_;
}
else
{
lean_object* v_resultDeps_2346_; uint8_t v___x_2347_; 
v_resultDeps_2346_ = lean_ctor_get(v_info_2308_, 1);
v___x_2347_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2346_, v_a_2312_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint8_t v_isProp_2349_; 
v___x_2348_ = lean_array_fget_borrowed(v___x_2310_, v_a_2312_);
v_isProp_2349_ = lean_ctor_get_uint8(v___x_2348_, sizeof(void*)*1 + 2);
if (v_isProp_2349_ == 0)
{
uint8_t v_isInstance_2350_; 
v_isInstance_2350_ = lean_ctor_get_uint8(v___x_2348_, sizeof(void*)*1 + 4);
if (v_isInstance_2350_ == 0)
{
uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = 2;
v___x_2352_ = lean_box(v___x_2351_);
v___x_2353_ = lean_array_push(v_b_2313_, v___x_2352_);
v_a_2320_ = v___x_2353_;
goto v___jp_2319_;
}
else
{
if (lean_obj_tag(v_a_2311_) == 1)
{
lean_object* v_val_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_val_2354_ = lean_ctor_get(v_a_2311_, 0);
v___x_2355_ = lean_array_get_size(v_val_2354_);
v___x_2356_ = lean_nat_dec_lt(v_a_2312_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2308_, v_a_2312_, v___x_2357_, v_b_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v___y_2325_ = v___x_2358_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_array_fget_borrowed(v_val_2354_, v_a_2312_);
v___x_2360_ = lean_unbox(v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_box(0);
v___x_2362_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2308_, v_a_2312_, v___x_2361_, v_b_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v___y_2325_ = v___x_2362_;
goto v___jp_2324_;
}
else
{
uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = 2;
v___x_2364_ = lean_box(v___x_2363_);
v___x_2365_ = lean_array_push(v_b_2313_, v___x_2364_);
v_a_2320_ = v___x_2365_;
goto v___jp_2319_;
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___lam__0(v_info_2308_, v_a_2312_, v___x_2366_, v_b_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v___y_2325_ = v___x_2367_;
goto v___jp_2324_;
}
}
}
else
{
uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = 3;
v___x_2369_ = lean_box(v___x_2368_);
v___x_2370_ = lean_array_push(v_b_2313_, v___x_2369_);
v_a_2320_ = v___x_2370_;
goto v___jp_2319_;
}
}
else
{
uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = 0;
v___x_2372_ = lean_box(v___x_2371_);
v___x_2373_ = lean_array_push(v_b_2313_, v___x_2372_);
v_a_2320_ = v___x_2373_;
goto v___jp_2319_;
}
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v_a_2312_, v___x_2321_);
lean_dec(v_a_2312_);
v_a_2312_ = v___x_2322_;
v_b_2313_ = v_a_2320_;
goto _start;
}
v___jp_2324_:
{
if (lean_obj_tag(v___y_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v_a_2326_ = lean_ctor_get(v___y_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___y_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___y_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___y_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
if (lean_obj_tag(v_a_2326_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; 
lean_dec(v_a_2312_);
v_a_2330_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v_a_2326_, 1);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_a_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_object* v_a_2334_; 
lean_del_object(v___x_2328_);
v_a_2334_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v_a_2326_, 1);
v_a_2320_ = v_a_2334_;
goto v___jp_2319_;
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2312_);
v_a_2336_ = lean_ctor_get(v___y_2325_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___y_2325_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___y_2325_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___y_2325_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2308_ = stack[0].m_obj;
lean_object* v_upperBound_2309_ = stack[1].m_obj;
lean_object* v___x_2310_ = stack[2].m_obj;
lean_object* v_a_2311_ = stack[3].m_obj;
lean_object* v_a_2312_ = stack[4].m_obj;
lean_object* v_b_2313_ = stack[5].m_obj;
lean_object* v___y_2314_ = stack[6].m_obj;
lean_object* v___y_2315_ = stack[7].m_obj;
lean_object* v___y_2316_ = stack[8].m_obj;
lean_object* v___y_2317_ = stack[9].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2308_, v_upperBound_2309_, v___x_2310_, v_a_2311_, v_a_2312_, v_b_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg___boxed(lean_object* v_info_2375_, lean_object* v_upperBound_2376_, lean_object* v___x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2375_, v_upperBound_2376_, v___x_2377_, v_a_2378_, v_a_2379_, v_b_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v_a_2378_);
lean_dec_ref(v___x_2377_);
lean_dec(v_upperBound_2376_);
lean_dec_ref(v_info_2375_);
return v_res_2386_;
}
}
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object* v_f_2389_, lean_object* v_info_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v_result_2397_; lean_object* v___x_2398_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v_result_2397_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2398_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f(v_f_2389_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v_paramInfo_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v_paramInfo_2400_ = lean_ctor_get(v_info_2390_, 0);
v___x_2401_ = lean_array_get_size(v_paramInfo_2400_);
v___x_2402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2390_, v___x_2401_, v_paramInfo_2400_, v_a_2399_, v___x_2396_, v_result_2397_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2399_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2411_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2390_, v_a_2403_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
else
{
return v___x_2402_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_a_2412_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2398_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2398_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getCongrSimpKinds_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2389_ = stack[0].m_obj;
lean_object* v_info_2390_ = stack[1].m_obj;
lean_object* v_a_2391_ = stack[2].m_obj;
lean_object* v_a_2392_ = stack[3].m_obj;
lean_object* v_a_2393_ = stack[4].m_obj;
lean_object* v_a_2394_ = stack[5].m_obj;
lean_object* v_res_2420_;
v_res_2420_ = l_Lean_Meta_getCongrSimpKinds(v_f_2389_, v_info_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKinds___boxed(lean_object* v_f_2421_, lean_object* v_info_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Meta_getCongrSimpKinds(v_f_2421_, v_info_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec_ref(v_info_2422_);
return v_res_2428_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(lean_object* v_info_2429_, lean_object* v_upperBound_2430_, lean_object* v___x_2431_, lean_object* v_a_2432_, lean_object* v_inst_2433_, lean_object* v_R_2434_, lean_object* v_a_2435_, lean_object* v_b_2436_, lean_object* v_c_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___redArg(v_info_2429_, v_upperBound_2430_, v___x_2431_, v_a_2432_, v_a_2435_, v_b_2436_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2429_ = stack[0].m_obj;
lean_object* v_upperBound_2430_ = stack[1].m_obj;
lean_object* v___x_2431_ = stack[2].m_obj;
lean_object* v_a_2432_ = stack[3].m_obj;
lean_object* v_a_2435_ = stack[6].m_obj;
lean_object* v_b_2436_ = stack[7].m_obj;
lean_object* v___y_2438_ = stack[9].m_obj;
lean_object* v___y_2439_ = stack[10].m_obj;
lean_object* v___y_2440_ = stack[11].m_obj;
lean_object* v___y_2441_ = stack[12].m_obj;
lean_object* v_res_2444_;
v_res_2444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2429_, v_upperBound_2430_, v___x_2431_, v_a_2432_, lean_box(0), lean_box(0), v_a_2435_, v_b_2436_, lean_box(0), v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
stack->m_obj
 = v_res_2444_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0___boxed(lean_object* v_info_2445_, lean_object* v_upperBound_2446_, lean_object* v___x_2447_, lean_object* v_a_2448_, lean_object* v_inst_2449_, lean_object* v_R_2450_, lean_object* v_a_2451_, lean_object* v_b_2452_, lean_object* v_c_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKinds_spec__0(v_info_2445_, v_upperBound_2446_, v___x_2447_, v_a_2448_, v_inst_2449_, v_R_2450_, v_a_2451_, v_b_2452_, v_c_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v_a_2448_);
lean_dec_ref(v___x_2447_);
lean_dec(v_upperBound_2446_);
lean_dec_ref(v_info_2445_);
return v_res_2459_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(lean_object* v_upperBound_2460_, lean_object* v_info_2461_, lean_object* v___x_2462_, lean_object* v_a_2463_, lean_object* v_b_2464_){
_start:
{
lean_object* v_a_2467_; uint8_t v___x_2471_; 
v___x_2471_ = lean_nat_dec_lt(v_a_2463_, v_upperBound_2460_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v_a_2463_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_b_2464_);
return v___x_2472_;
}
else
{
lean_object* v_resultDeps_2473_; uint8_t v___x_2474_; 
v_resultDeps_2473_ = lean_ctor_get(v_info_2461_, 1);
v___x_2474_ = l_Array_contains___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies_spec__0(v_resultDeps_2473_, v_a_2463_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = lean_nat_dec_eq(v_a_2463_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; uint8_t v_isProp_2478_; 
v___x_2477_ = lean_array_fget_borrowed(v___x_2462_, v_a_2463_);
v_isProp_2478_ = lean_ctor_get_uint8(v___x_2477_, sizeof(void*)*1 + 2);
if (v_isProp_2478_ == 0)
{
uint8_t v_isInstance_2479_; 
v_isInstance_2479_ = lean_ctor_get_uint8(v___x_2477_, sizeof(void*)*1 + 4);
if (v_isInstance_2479_ == 0)
{
uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = 0;
v___x_2481_ = lean_box(v___x_2480_);
v___x_2482_ = lean_array_push(v_b_2464_, v___x_2481_);
v_a_2467_ = v___x_2482_;
goto v___jp_2466_;
}
else
{
uint8_t v___x_2483_; 
v___x_2483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_shouldUseSubsingletonInst(v_info_2461_, v_b_2464_, v_a_2463_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = 0;
v___x_2485_ = lean_box(v___x_2484_);
v___x_2486_ = lean_array_push(v_b_2464_, v___x_2485_);
v_a_2467_ = v___x_2486_;
goto v___jp_2466_;
}
else
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = 5;
v___x_2488_ = lean_box(v___x_2487_);
v___x_2489_ = lean_array_push(v_b_2464_, v___x_2488_);
v_a_2467_ = v___x_2489_;
goto v___jp_2466_;
}
}
}
else
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = 3;
v___x_2491_ = lean_box(v___x_2490_);
v___x_2492_ = lean_array_push(v_b_2464_, v___x_2491_);
v_a_2467_ = v___x_2492_;
goto v___jp_2466_;
}
}
else
{
uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = 2;
v___x_2494_ = lean_box(v___x_2493_);
v___x_2495_ = lean_array_push(v_b_2464_, v___x_2494_);
v_a_2467_ = v___x_2495_;
goto v___jp_2466_;
}
}
else
{
uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = 0;
v___x_2497_ = lean_box(v___x_2496_);
v___x_2498_ = lean_array_push(v_b_2464_, v___x_2497_);
v_a_2467_ = v___x_2498_;
goto v___jp_2466_;
}
}
v___jp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_nat_add(v_a_2463_, v___x_2468_);
lean_dec(v_a_2463_);
v_a_2463_ = v___x_2469_;
v_b_2464_ = v_a_2467_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2460_ = stack[0].m_obj;
lean_object* v_info_2461_ = stack[1].m_obj;
lean_object* v___x_2462_ = stack[2].m_obj;
lean_object* v_a_2463_ = stack[3].m_obj;
lean_object* v_b_2464_ = stack[4].m_obj;
lean_object* v_res_2499_;
v_res_2499_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2460_, v_info_2461_, v___x_2462_, v_a_2463_, v_b_2464_);
stack->m_obj
 = v_res_2499_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg___boxed(lean_object* v_upperBound_2500_, lean_object* v_info_2501_, lean_object* v___x_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2500_, v_info_2501_, v___x_2502_, v_a_2503_, v_b_2504_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v_info_2501_);
lean_dec(v_upperBound_2500_);
return v_res_2506_;
}
}
lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object* v_info_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_paramInfo_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_result_2516_; lean_object* v___x_2517_; 
v_paramInfo_2513_ = lean_ctor_get(v_info_2507_, 0);
v___x_2514_ = lean_array_get_size(v_paramInfo_2513_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v_result_2516_ = ((lean_object*)(l_Lean_Meta_getCongrSimpKinds___closed__0));
v___x_2517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v___x_2514_, v_info_2507_, v_paramInfo_2513_, v___x_2515_, v_result_2516_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_fixKindsForDependencies(v_info_2507_, v_a_2518_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
return v___x_2517_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getCongrSimpKindsForArgZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2507_ = stack[0].m_obj;
lean_object* v_a_2508_ = stack[1].m_obj;
lean_object* v_a_2509_ = stack[2].m_obj;
lean_object* v_a_2510_ = stack[3].m_obj;
lean_object* v_a_2511_ = stack[4].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero___boxed(lean_object* v_info_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_info_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec_ref(v_info_2528_);
return v_res_2534_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(lean_object* v_upperBound_2535_, lean_object* v_info_2536_, lean_object* v___x_2537_, lean_object* v_inst_2538_, lean_object* v_R_2539_, lean_object* v_a_2540_, lean_object* v_b_2541_, lean_object* v_c_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___redArg(v_upperBound_2535_, v_info_2536_, v___x_2537_, v_a_2540_, v_b_2541_);
return v___x_2548_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2535_ = stack[0].m_obj;
lean_object* v_info_2536_ = stack[1].m_obj;
lean_object* v___x_2537_ = stack[2].m_obj;
lean_object* v_a_2540_ = stack[5].m_obj;
lean_object* v_b_2541_ = stack[6].m_obj;
lean_object* v___y_2543_ = stack[8].m_obj;
lean_object* v___y_2544_ = stack[9].m_obj;
lean_object* v___y_2545_ = stack[10].m_obj;
lean_object* v___y_2546_ = stack[11].m_obj;
lean_object* v_res_2549_;
v_res_2549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2535_, v_info_2536_, v___x_2537_, lean_box(0), lean_box(0), v_a_2540_, v_b_2541_, lean_box(0), v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
stack->m_obj
 = v_res_2549_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0___boxed(lean_object* v_upperBound_2550_, lean_object* v_info_2551_, lean_object* v___x_2552_, lean_object* v_inst_2553_, lean_object* v_R_2554_, lean_object* v_a_2555_, lean_object* v_b_2556_, lean_object* v_c_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCongrSimpKindsForArgZero_spec__0(v_upperBound_2550_, v_info_2551_, v___x_2552_, v_inst_2553_, v_R_2554_, v_a_2555_, v_b_2556_, v_c_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec_ref(v___x_2552_);
lean_dec_ref(v_info_2551_);
lean_dec(v_upperBound_2550_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(lean_object* v_x_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_obj_tag_nat(v_x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl___boxed(lean_object* v_x_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorIdx___impl(v_x_2566_);
lean_dec_ref(v_x_2566_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(lean_object* v_t_2568_, lean_object* v_k_2569_){
_start:
{
if (lean_obj_tag(v_t_2568_) == 0)
{
lean_object* v_fvarId_2570_; lean_object* v___x_2571_; 
v_fvarId_2570_ = lean_ctor_get(v_t_2568_, 0);
lean_inc(v_fvarId_2570_);
lean_dec_ref_known(v_t_2568_, 1);
v___x_2571_ = lean_apply_1(v_k_2569_, v_fvarId_2570_);
return v___x_2571_;
}
else
{
lean_object* v_lhs_2572_; lean_object* v_rhs_2573_; lean_object* v___x_2574_; 
v_lhs_2572_ = lean_ctor_get(v_t_2568_, 0);
lean_inc(v_lhs_2572_);
v_rhs_2573_ = lean_ctor_get(v_t_2568_, 1);
lean_inc(v_rhs_2573_);
lean_dec_ref_known(v_t_2568_, 2);
v___x_2574_ = lean_apply_2(v_k_2569_, v_lhs_2572_, v_rhs_2573_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(lean_object* v_motive_2575_, lean_object* v_ctorIdx_2576_, lean_object* v_t_2577_, lean_object* v_h_2578_, lean_object* v_k_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2577_, v_k_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___boxed(lean_object* v_motive_2581_, lean_object* v_ctorIdx_2582_, lean_object* v_t_2583_, lean_object* v_h_2584_, lean_object* v_k_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim(v_motive_2581_, v_ctorIdx_2582_, v_t_2583_, v_h_2584_, v_k_2585_);
lean_dec(v_ctorIdx_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim___redArg(lean_object* v_t_2587_, lean_object* v_hyp_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2587_, v_hyp_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_hyp_elim(lean_object* v_motive_2590_, lean_object* v_t_2591_, lean_object* v_h_2592_, lean_object* v_hyp_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2591_, v_hyp_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim___redArg(lean_object* v_t_2595_, lean_object* v_decSubsingleton_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2595_, v_decSubsingleton_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_decSubsingleton_elim(lean_object* v_motive_2598_, lean_object* v_t_2599_, lean_object* v_h_2600_, lean_object* v_decSubsingleton_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_EqInfo_ctorElim___redArg(v_t_2599_, v_decSubsingleton_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(lean_object* v_s_2603_, lean_object* v_fvarId_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_2603_, v_fvarId_2604_);
if (lean_obj_tag(v___x_2605_) == 1)
{
lean_object* v_val_2606_; lean_object* v___x_2607_; 
v_val_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = l_Lean_Expr_fvarId_x21(v_val_2606_);
lean_dec(v_val_2606_);
return v___x_2607_;
}
else
{
lean_dec(v___x_2605_);
lean_inc(v_fvarId_2604_);
return v_fvarId_2604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId___boxed(lean_object* v_s_2608_, lean_object* v_fvarId_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_s_2608_, v_fvarId_2609_);
lean_dec(v_fvarId_2609_);
lean_dec(v_s_2608_);
return v_res_2610_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(lean_object* v_mvarId_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2611_, v_x_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2618_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2618_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2611_ = stack[0].m_obj;
lean_object* v_x_2612_ = stack[1].m_obj;
lean_object* v___y_2613_ = stack[2].m_obj;
lean_object* v___y_2614_ = stack[3].m_obj;
lean_object* v___y_2615_ = stack[4].m_obj;
lean_object* v___y_2616_ = stack[5].m_obj;
lean_object* v_res_2635_;
v_res_2635_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2611_, v_x_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
stack->m_obj
 = v_res_2635_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg___boxed(lean_object* v_mvarId_2636_, lean_object* v_x_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2636_, v_x_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2643_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_object* v_00_u03b1_2644_, lean_object* v_mvarId_2645_, lean_object* v_x_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_mvarId_2645_, v_x_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2645_ = stack[1].m_obj;
lean_object* v_x_2646_ = stack[2].m_obj;
lean_object* v___y_2647_ = stack[3].m_obj;
lean_object* v___y_2648_ = stack[4].m_obj;
lean_object* v___y_2649_ = stack[5].m_obj;
lean_object* v___y_2650_ = stack[6].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(lean_box(0), v_mvarId_2645_, v_x_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___boxed(lean_object* v_00_u03b1_2654_, lean_object* v_mvarId_2655_, lean_object* v_x_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1(v_00_u03b1_2654_, v_mvarId_2655_, v_x_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2662_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(lean_object* v_e_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = l_Lean_Expr_hasMVar(v_e_2663_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_e_2663_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; lean_object* v_mctx_2669_; lean_object* v___x_2670_; lean_object* v_fst_2671_; lean_object* v_snd_2672_; lean_object* v___x_2673_; lean_object* v_cache_2674_; lean_object* v_zetaDeltaFVarIds_2675_; lean_object* v_postponed_2676_; lean_object* v_diag_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2686_; 
v___x_2668_ = lean_st_ref_get(v___y_2664_);
v_mctx_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_mctx_2669_);
lean_dec(v___x_2668_);
v___x_2670_ = l_Lean_instantiateMVarsCore(v_mctx_2669_, v_e_2663_);
v_fst_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_fst_2671_);
v_snd_2672_ = lean_ctor_get(v___x_2670_, 1);
lean_inc(v_snd_2672_);
lean_dec_ref(v___x_2670_);
v___x_2673_ = lean_st_ref_take(v___y_2664_);
v_cache_2674_ = lean_ctor_get(v___x_2673_, 1);
v_zetaDeltaFVarIds_2675_ = lean_ctor_get(v___x_2673_, 2);
v_postponed_2676_ = lean_ctor_get(v___x_2673_, 3);
v_diag_2677_ = lean_ctor_get(v___x_2673_, 4);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2673_, 0);
lean_dec(v_unused_2687_);
v___x_2679_ = v___x_2673_;
v_isShared_2680_ = v_isSharedCheck_2686_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_diag_2677_);
lean_inc(v_postponed_2676_);
lean_inc(v_zetaDeltaFVarIds_2675_);
lean_inc(v_cache_2674_);
lean_dec(v___x_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2686_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v_snd_2672_);
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_snd_2672_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_cache_2674_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_zetaDeltaFVarIds_2675_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_postponed_2676_);
lean_ctor_set(v_reuseFailAlloc_2685_, 4, v_diag_2677_);
v___x_2682_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_st_ref_put(v___y_2664_, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_fst_2671_);
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2663_ = stack[0].m_obj;
lean_object* v___y_2664_ = stack[1].m_obj;
lean_object* v_res_2688_;
v_res_2688_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2663_, v___y_2664_);
stack->m_obj
 = v_res_2688_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg___boxed(lean_object* v_e_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2689_, v___y_2690_);
lean_dec(v___y_2690_);
return v_res_2692_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(lean_object* v_e_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_e_2693_, v___y_2695_);
return v___x_2699_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2693_ = stack[0].m_obj;
lean_object* v___y_2694_ = stack[1].m_obj;
lean_object* v___y_2695_ = stack[2].m_obj;
lean_object* v___y_2696_ = stack[3].m_obj;
lean_object* v___y_2697_ = stack[4].m_obj;
lean_object* v_res_2700_;
v_res_2700_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
stack->m_obj
 = v_res_2700_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___boxed(lean_object* v_e_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4(v_e_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v_ks_2712_; lean_object* v_vs_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2737_; 
v_ks_2712_ = lean_ctor_get(v_x_2708_, 0);
v_vs_2713_ = lean_ctor_get(v_x_2708_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2715_ = v_x_2708_;
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_vs_2713_);
lean_inc(v_ks_2712_);
lean_dec(v_x_2708_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = lean_array_get_size(v_ks_2712_);
v___x_2718_ = lean_nat_dec_lt(v_x_2709_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_dec(v_x_2709_);
v___x_2719_ = lean_array_push(v_ks_2712_, v_x_2710_);
v___x_2720_ = lean_array_push(v_vs_2713_, v_x_2711_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2720_);
lean_ctor_set(v___x_2715_, 0, v___x_2719_);
v___x_2722_ = v___x_2715_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
else
{
lean_object* v_k_x27_2724_; uint8_t v___x_2725_; 
v_k_x27_2724_ = lean_array_fget_borrowed(v_ks_2712_, v_x_2709_);
v___x_2725_ = l_Lean_instBEqMVarId_beq(v_x_2710_, v_k_x27_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; 
if (v_isShared_2716_ == 0)
{
v___x_2727_ = v___x_2715_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_ks_2712_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_vs_2713_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_add(v_x_2709_, v___x_2728_);
lean_dec(v_x_2709_);
v_x_2708_ = v___x_2727_;
v_x_2709_ = v___x_2729_;
goto _start;
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_array_fset(v_ks_2712_, v_x_2709_, v_x_2710_);
v___x_2733_ = lean_array_fset(v_vs_2713_, v_x_2709_, v_x_2711_);
lean_dec(v_x_2709_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2733_);
lean_ctor_set(v___x_2715_, 0, v___x_2732_);
v___x_2735_ = v___x_2715_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_2738_, lean_object* v_k_2739_, lean_object* v_v_2740_){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_2738_, v___x_2741_, v_k_2739_, v_v_2740_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2743_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(lean_object* v_x_2744_, size_t v_x_2745_, size_t v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
if (lean_obj_tag(v_x_2744_) == 0)
{
lean_object* v_es_2749_; size_t v___x_2750_; size_t v___x_2751_; lean_object* v_j_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_es_2749_ = lean_ctor_get(v_x_2744_, 0);
v___x_2750_ = ((size_t)31ULL);
v___x_2751_ = lean_usize_land(v_x_2745_, v___x_2750_);
v_j_2752_ = lean_usize_to_nat(v___x_2751_);
v___x_2753_ = lean_array_get_size(v_es_2749_);
v___x_2754_ = lean_nat_dec_lt(v_j_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_dec(v_j_2752_);
lean_dec(v_x_2748_);
lean_dec(v_x_2747_);
return v_x_2744_;
}
else
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2793_; 
lean_inc_ref(v_es_2749_);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_x_2744_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_x_2744_, 0);
lean_dec(v_unused_2794_);
v___x_2756_ = v_x_2744_;
v_isShared_2757_ = v_isSharedCheck_2793_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v_x_2744_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2793_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_v_2758_; lean_object* v___x_2759_; lean_object* v_xs_x27_2760_; lean_object* v___y_2762_; 
v_v_2758_ = lean_array_fget(v_es_2749_, v_j_2752_);
v___x_2759_ = lean_box(0);
v_xs_x27_2760_ = lean_array_fset(v_es_2749_, v_j_2752_, v___x_2759_);
switch(lean_obj_tag(v_v_2758_))
{
case 0:
{
lean_object* v_key_2767_; lean_object* v_val_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2778_; 
v_key_2767_ = lean_ctor_get(v_v_2758_, 0);
v_val_2768_ = lean_ctor_get(v_v_2758_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_v_2758_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2770_ = v_v_2758_;
v_isShared_2771_ = v_isSharedCheck_2778_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_val_2768_);
lean_inc(v_key_2767_);
lean_dec(v_v_2758_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2778_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
uint8_t v___x_2772_; 
v___x_2772_ = l_Lean_instBEqMVarId_beq(v_x_2747_, v_key_2767_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_del_object(v___x_2770_);
v___x_2773_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2767_, v_val_2768_, v_x_2747_, v_x_2748_);
v___x_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
v___y_2762_ = v___x_2774_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2776_; 
lean_dec(v_val_2768_);
lean_dec(v_key_2767_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v_x_2748_);
lean_ctor_set(v___x_2770_, 0, v_x_2747_);
v___x_2776_ = v___x_2770_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_x_2747_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_x_2748_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v___y_2762_ = v___x_2776_;
goto v___jp_2761_;
}
}
}
}
case 1:
{
lean_object* v_node_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2791_; 
v_node_2779_ = lean_ctor_get(v_v_2758_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_v_2758_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2781_ = v_v_2758_;
v_isShared_2782_ = v_isSharedCheck_2791_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_node_2779_);
lean_dec(v_v_2758_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2791_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
size_t v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2783_ = ((size_t)5ULL);
v___x_2784_ = lean_usize_shift_right(v_x_2745_, v___x_2783_);
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_add(v_x_2746_, v___x_2785_);
v___x_2787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_node_2779_, v___x_2784_, v___x_2786_, v_x_2747_, v_x_2748_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2787_);
v___x_2789_ = v___x_2781_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
v___y_2762_ = v___x_2789_;
goto v___jp_2761_;
}
}
}
default: 
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_x_2747_);
lean_ctor_set(v___x_2792_, 1, v_x_2748_);
v___y_2762_ = v___x_2792_;
goto v___jp_2761_;
}
}
v___jp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = lean_array_fset(v_xs_x27_2760_, v_j_2752_, v___y_2762_);
lean_dec(v_j_2752_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2763_);
v___x_2765_ = v___x_2756_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
else
{
lean_object* v_ks_2795_; lean_object* v_vs_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2814_; 
v_ks_2795_ = lean_ctor_get(v_x_2744_, 0);
v_vs_2796_ = lean_ctor_get(v_x_2744_, 1);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_x_2744_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2798_ = v_x_2744_;
v_isShared_2799_ = v_isSharedCheck_2814_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_vs_2796_);
lean_inc(v_ks_2795_);
lean_dec(v_x_2744_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2814_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_ks_2795_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_vs_2796_);
v___x_2801_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v_newNode_2802_; size_t v___x_2803_; uint8_t v___x_2804_; 
v_newNode_2802_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v___x_2801_, v_x_2747_, v_x_2748_);
v___x_2803_ = ((size_t)7ULL);
v___x_2804_ = lean_usize_dec_le(v___x_2803_, v_x_2746_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2805_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2802_);
v___x_2806_ = lean_unsigned_to_nat(4u);
v___x_2807_ = lean_nat_dec_lt(v___x_2805_, v___x_2806_);
lean_dec(v___x_2805_);
if (v___x_2807_ == 0)
{
lean_object* v_ks_2808_; lean_object* v_vs_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_ks_2808_ = lean_ctor_get(v_newNode_2802_, 0);
lean_inc_ref(v_ks_2808_);
v_vs_2809_ = lean_ctor_get(v_newNode_2802_, 1);
lean_inc_ref(v_vs_2809_);
lean_dec_ref(v_newNode_2802_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_2812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_x_2746_, v_ks_2808_, v_vs_2809_, v___x_2810_, v___x_2811_);
lean_dec_ref(v_vs_2809_);
lean_dec_ref(v_ks_2808_);
return v___x_2812_;
}
else
{
return v_newNode_2802_;
}
}
else
{
return v_newNode_2802_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2744_ = stack[0].m_obj;
size_t v_x_2745_ = stack[1].m_num;
size_t v_x_2746_ = stack[2].m_num;
lean_object* v_x_2747_ = stack[3].m_obj;
lean_object* v_x_2748_ = stack[4].m_obj;
lean_object* v_res_2815_;
v_res_2815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2744_, v_x_2745_, v_x_2746_, v_x_2747_, v_x_2748_);
stack->m_obj
 = v_res_2815_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_2816_, lean_object* v_keys_2817_, lean_object* v_vals_2818_, lean_object* v_i_2819_, lean_object* v_entries_2820_){
_start:
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_array_get_size(v_keys_2817_);
v___x_2822_ = lean_nat_dec_lt(v_i_2819_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec(v_i_2819_);
return v_entries_2820_;
}
else
{
lean_object* v_k_2823_; lean_object* v_v_2824_; uint64_t v___x_2825_; size_t v_h_2826_; size_t v___x_2827_; lean_object* v___x_2828_; size_t v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; size_t v_h_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_k_2823_ = lean_array_fget_borrowed(v_keys_2817_, v_i_2819_);
v_v_2824_ = lean_array_fget_borrowed(v_vals_2818_, v_i_2819_);
v___x_2825_ = l_Lean_instHashableMVarId_hash(v_k_2823_);
v_h_2826_ = lean_uint64_to_usize(v___x_2825_);
v___x_2827_ = ((size_t)5ULL);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_sub(v_depth_2816_, v___x_2829_);
v___x_2831_ = lean_usize_mul(v___x_2827_, v___x_2830_);
v_h_2832_ = lean_usize_shift_right(v_h_2826_, v___x_2831_);
v___x_2833_ = lean_nat_add(v_i_2819_, v___x_2828_);
lean_dec(v_i_2819_);
lean_inc(v_v_2824_);
lean_inc(v_k_2823_);
v___x_2834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_entries_2820_, v_h_2832_, v_depth_2816_, v_k_2823_, v_v_2824_);
v_i_2819_ = v___x_2833_;
v_entries_2820_ = v___x_2834_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2816_ = stack[0].m_num;
lean_object* v_keys_2817_ = stack[1].m_obj;
lean_object* v_vals_2818_ = stack[2].m_obj;
lean_object* v_i_2819_ = stack[3].m_obj;
lean_object* v_entries_2820_ = stack[4].m_obj;
lean_object* v_res_2836_;
v_res_2836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_2816_, v_keys_2817_, v_vals_2818_, v_i_2819_, v_entries_2820_);
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_2837_, lean_object* v_keys_2838_, lean_object* v_vals_2839_, lean_object* v_i_2840_, lean_object* v_entries_2841_){
_start:
{
size_t v_depth_boxed_2842_; lean_object* v_res_2843_; 
v_depth_boxed_2842_ = lean_unbox_usize(v_depth_2837_);
lean_dec(v_depth_2837_);
v_res_2843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_2842_, v_keys_2838_, v_vals_2839_, v_i_2840_, v_entries_2841_);
lean_dec_ref(v_vals_2839_);
lean_dec_ref(v_keys_2838_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_){
_start:
{
size_t v_x_3988__boxed_2849_; size_t v_x_3989__boxed_2850_; lean_object* v_res_2851_; 
v_x_3988__boxed_2849_ = lean_unbox_usize(v_x_2845_);
lean_dec(v_x_2845_);
v_x_3989__boxed_2850_ = lean_unbox_usize(v_x_2846_);
lean_dec(v_x_2846_);
v_res_2851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2844_, v_x_3988__boxed_2849_, v_x_3989__boxed_2850_, v_x_2847_, v_x_2848_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(lean_object* v_x_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
uint64_t v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = l_Lean_instHashableMVarId_hash(v_x_2853_);
v___x_2856_ = lean_uint64_to_usize(v___x_2855_);
v___x_2857_ = ((size_t)1ULL);
v___x_2858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_2852_, v___x_2856_, v___x_2857_, v_x_2853_, v_x_2854_);
return v___x_2858_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(lean_object* v_mvarId_2859_, lean_object* v_val_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v_mctx_2864_; lean_object* v_cache_2865_; lean_object* v_zetaDeltaFVarIds_2866_; lean_object* v_postponed_2867_; lean_object* v_diag_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2898_; 
v___x_2863_ = lean_st_ref_take(v___y_2861_);
v_mctx_2864_ = lean_ctor_get(v___x_2863_, 0);
v_cache_2865_ = lean_ctor_get(v___x_2863_, 1);
v_zetaDeltaFVarIds_2866_ = lean_ctor_get(v___x_2863_, 2);
v_postponed_2867_ = lean_ctor_get(v___x_2863_, 3);
v_diag_2868_ = lean_ctor_get(v___x_2863_, 4);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2870_ = v___x_2863_;
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_diag_2868_);
lean_inc(v_postponed_2867_);
lean_inc(v_zetaDeltaFVarIds_2866_);
lean_inc(v_cache_2865_);
lean_inc(v_mctx_2864_);
lean_dec(v___x_2863_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_depth_2872_; lean_object* v_levelAssignDepth_2873_; lean_object* v_lmvarCounter_2874_; lean_object* v_mvarCounter_2875_; lean_object* v_lDecls_2876_; lean_object* v_decls_2877_; lean_object* v_userNames_2878_; lean_object* v_lAssignment_2879_; lean_object* v_eAssignment_2880_; lean_object* v_dAssignment_2881_; lean_object* v_instanceTypedMVars_2882_; lean_object* v_synthNormMemo_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2897_; 
v_depth_2872_ = lean_ctor_get(v_mctx_2864_, 0);
v_levelAssignDepth_2873_ = lean_ctor_get(v_mctx_2864_, 1);
v_lmvarCounter_2874_ = lean_ctor_get(v_mctx_2864_, 2);
v_mvarCounter_2875_ = lean_ctor_get(v_mctx_2864_, 3);
v_lDecls_2876_ = lean_ctor_get(v_mctx_2864_, 4);
v_decls_2877_ = lean_ctor_get(v_mctx_2864_, 5);
v_userNames_2878_ = lean_ctor_get(v_mctx_2864_, 6);
v_lAssignment_2879_ = lean_ctor_get(v_mctx_2864_, 7);
v_eAssignment_2880_ = lean_ctor_get(v_mctx_2864_, 8);
v_dAssignment_2881_ = lean_ctor_get(v_mctx_2864_, 9);
v_instanceTypedMVars_2882_ = lean_ctor_get(v_mctx_2864_, 10);
v_synthNormMemo_2883_ = lean_ctor_get(v_mctx_2864_, 11);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_mctx_2864_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2885_ = v_mctx_2864_;
v_isShared_2886_ = v_isSharedCheck_2897_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_synthNormMemo_2883_);
lean_inc(v_instanceTypedMVars_2882_);
lean_inc(v_dAssignment_2881_);
lean_inc(v_eAssignment_2880_);
lean_inc(v_lAssignment_2879_);
lean_inc(v_userNames_2878_);
lean_inc(v_decls_2877_);
lean_inc(v_lDecls_2876_);
lean_inc(v_mvarCounter_2875_);
lean_inc(v_lmvarCounter_2874_);
lean_inc(v_levelAssignDepth_2873_);
lean_inc(v_depth_2872_);
lean_dec(v_mctx_2864_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2897_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2887_ = lean_box(0);
v___x_2888_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_eAssignment_2880_, v_mvarId_2859_, v_val_2860_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 8, v___x_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_depth_2872_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_levelAssignDepth_2873_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_lmvarCounter_2874_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_mvarCounter_2875_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_lDecls_2876_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_decls_2877_);
lean_ctor_set(v_reuseFailAlloc_2896_, 6, v_userNames_2878_);
lean_ctor_set(v_reuseFailAlloc_2896_, 7, v_lAssignment_2879_);
lean_ctor_set(v_reuseFailAlloc_2896_, 8, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2896_, 9, v_dAssignment_2881_);
lean_ctor_set(v_reuseFailAlloc_2896_, 10, v_instanceTypedMVars_2882_);
lean_ctor_set(v_reuseFailAlloc_2896_, 11, v_synthNormMemo_2883_);
v___x_2890_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2892_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2890_);
v___x_2892_ = v___x_2870_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_cache_2865_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_zetaDeltaFVarIds_2866_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_postponed_2867_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_diag_2868_);
v___x_2892_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_st_ref_put(v___y_2861_, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2887_);
return v___x_2894_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2859_ = stack[0].m_obj;
lean_object* v_val_2860_ = stack[1].m_obj;
lean_object* v___y_2861_ = stack[2].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2859_, v_val_2860_, v___y_2861_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg___boxed(lean_object* v_mvarId_2900_, lean_object* v_val_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_2900_, v_val_2901_, v___y_2902_);
lean_dec(v___y_2902_);
return v_res_2904_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(lean_object* v___x_2913_, lean_object* v_as_2914_, size_t v_sz_2915_, size_t v_i_2916_, lean_object* v_b_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_a_2924_; uint8_t v___x_2928_; 
v___x_2928_ = lean_usize_dec_lt(v_i_2916_, v_sz_2915_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_b_2917_);
return v___x_2929_;
}
else
{
lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v_a_2934_; 
v_fst_2930_ = lean_ctor_get(v_b_2917_, 0);
lean_inc(v_fst_2930_);
v_snd_2931_ = lean_ctor_get(v_b_2917_, 1);
lean_inc(v_snd_2931_);
lean_dec_ref(v_b_2917_);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = lean_nat_dec_eq(v___x_2913_, v___x_2932_);
v_a_2934_ = lean_array_uget_borrowed(v_as_2914_, v_i_2916_);
if (lean_obj_tag(v_a_2934_) == 0)
{
lean_object* v_fvarId_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_fvarId_2935_ = lean_ctor_get(v_a_2934_, 0);
v___x_2936_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2931_, v_fvarId_2935_);
v___x_2937_ = l_Lean_Meta_substCore(v_fst_2930_, v___x_2936_, v___x_2928_, v_snd_2931_, v___x_2928_, v___x_2933_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v_fst_2939_; lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v_fst_2939_ = lean_ctor_get(v_a_2938_, 0);
v_snd_2940_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v_a_2938_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_inc(v_fst_2939_);
lean_dec(v_a_2938_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_fst_2939_);
lean_ctor_set(v___x_2942_, 0, v_snd_2940_);
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_snd_2940_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_fst_2939_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
v_a_2924_ = v___x_2945_;
goto v___jp_2923_;
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2937_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2937_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_lhs_2956_; lean_object* v_rhs_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_lhs_2956_ = lean_ctor_get(v_a_2934_, 0);
v_rhs_2957_ = lean_ctor_get(v_a_2934_, 1);
v___x_2958_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2931_, v_lhs_2956_);
v___x_2959_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_2931_, v_rhs_2957_);
v___x_2960_ = l_Lean_mkFVar(v___x_2958_);
v___x_2961_ = l_Lean_mkFVar(v___x_2959_);
lean_inc_ref(v___x_2961_);
lean_inc_ref(v___x_2960_);
v___x_2962_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_2962_, 0, v___x_2960_);
lean_closure_set(v___x_2962_, 1, v___x_2961_);
lean_inc(v_fst_2930_);
v___x_2963_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2930_, v___x_2962_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_2966_ = lean_unsigned_to_nat(2u);
v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
v___x_2968_ = lean_array_push(v___x_2967_, v___x_2960_);
v___x_2969_ = lean_array_push(v___x_2968_, v___x_2961_);
v___x_2970_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2970_, 0, v___x_2965_);
lean_closure_set(v___x_2970_, 1, v___x_2969_);
lean_inc(v_fst_2930_);
v___x_2971_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__1___redArg(v_fst_2930_, v___x_2970_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__4));
v___x_2974_ = l_Lean_MVarId_assert(v_fst_2930_, v___x_2973_, v_a_2964_, v_a_2972_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = l_Lean_Meta_intro1Core(v_a_2975_, v___x_2933_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v_fst_2978_; lean_object* v_snd_2979_; lean_object* v___x_2980_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
v_fst_2978_ = lean_ctor_get(v_a_2977_, 0);
lean_inc(v_fst_2978_);
v_snd_2979_ = lean_ctor_get(v_a_2977_, 1);
lean_inc(v_snd_2979_);
lean_dec(v_a_2977_);
v___x_2980_ = l_Lean_Meta_substCore(v_snd_2979_, v_fst_2978_, v___x_2928_, v_snd_2931_, v___x_2928_, v___x_2933_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_fst_2982_; lean_object* v_snd_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_fst_2982_ = lean_ctor_get(v_a_2981_, 0);
v_snd_2983_ = lean_ctor_get(v_a_2981_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_a_2981_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v_a_2981_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_snd_2983_);
lean_inc(v_fst_2982_);
lean_dec(v_a_2981_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v_fst_2982_);
lean_ctor_set(v___x_2985_, 0, v_snd_2983_);
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_snd_2983_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_fst_2982_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v_a_2924_ = v___x_2988_;
goto v___jp_2923_;
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2991_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2980_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2980_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_snd_2931_);
v_a_2999_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2976_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2976_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_snd_2931_);
v_a_3007_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2974_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2974_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_a_2964_);
lean_dec(v_snd_2931_);
lean_dec(v_fst_2930_);
v_a_3015_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2971_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2971_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2960_);
lean_dec(v_snd_2931_);
lean_dec(v_fst_2930_);
v_a_3023_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2963_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2963_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
v___jp_2923_:
{
size_t v___x_2925_; size_t v___x_2926_; 
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2916_, v___x_2925_);
v_i_2916_ = v___x_2926_;
v_b_2917_ = v_a_2924_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2913_ = stack[0].m_obj;
lean_object* v_as_2914_ = stack[1].m_obj;
size_t v_sz_2915_ = stack[2].m_num;
size_t v_i_2916_ = stack[3].m_num;
lean_object* v_b_2917_ = stack[4].m_obj;
lean_object* v___y_2918_ = stack[5].m_obj;
lean_object* v___y_2919_ = stack[6].m_obj;
lean_object* v___y_2920_ = stack[7].m_obj;
lean_object* v___y_2921_ = stack[8].m_obj;
lean_object* v_res_3031_;
v_res_3031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_2913_, v_as_2914_, v_sz_2915_, v_i_2916_, v_b_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
stack->m_obj
 = v_res_3031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___boxed(lean_object* v___x_3032_, lean_object* v_as_3033_, lean_object* v_sz_3034_, lean_object* v_i_3035_, lean_object* v_b_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
size_t v_sz_boxed_3042_; size_t v_i_boxed_3043_; lean_object* v_res_3044_; 
v_sz_boxed_3042_ = lean_unbox_usize(v_sz_3034_);
lean_dec(v_sz_3034_);
v_i_boxed_3043_ = lean_unbox_usize(v_i_3035_);
lean_dec(v_i_3035_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3032_, v_as_3033_, v_sz_boxed_3042_, v_i_boxed_3043_, v_b_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec_ref(v_as_3033_);
lean_dec(v___x_3032_);
return v_res_3044_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(lean_object* v_eqs_3045_, lean_object* v_as_3046_, size_t v_i_3047_, size_t v_stop_3048_, lean_object* v_b_3049_){
_start:
{
lean_object* v___y_3051_; uint8_t v___x_3055_; 
v___x_3055_ = lean_usize_dec_eq(v_i_3047_, v_stop_3048_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = lean_box(0);
v___x_3057_ = lean_array_uget_borrowed(v_as_3046_, v_i_3047_);
v___x_3058_ = lean_array_get_borrowed(v___x_3056_, v_eqs_3045_, v___x_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
v___y_3051_ = v_b_3049_;
goto v___jp_3050_;
}
else
{
lean_object* v_val_3059_; lean_object* v___x_3060_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3059_);
v___x_3060_ = lean_array_push(v_b_3049_, v_val_3059_);
v___y_3051_ = v___x_3060_;
goto v___jp_3050_;
}
}
else
{
return v_b_3049_;
}
v___jp_3050_:
{
size_t v___x_3052_; size_t v___x_3053_; 
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_add(v_i_3047_, v___x_3052_);
v_i_3047_ = v___x_3053_;
v_b_3049_ = v___y_3051_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqs_3045_ = stack[0].m_obj;
lean_object* v_as_3046_ = stack[1].m_obj;
size_t v_i_3047_ = stack[2].m_num;
size_t v_stop_3048_ = stack[3].m_num;
lean_object* v_b_3049_ = stack[4].m_obj;
lean_object* v_res_3061_;
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_3045_, v_as_3046_, v_i_3047_, v_stop_3048_, v_b_3049_);
stack->m_obj
 = v_res_3061_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0___boxed(lean_object* v_eqs_3062_, lean_object* v_as_3063_, lean_object* v_i_3064_, lean_object* v_stop_3065_, lean_object* v_b_3066_){
_start:
{
size_t v_i_boxed_3067_; size_t v_stop_boxed_3068_; lean_object* v_res_3069_; 
v_i_boxed_3067_ = lean_unbox_usize(v_i_3064_);
lean_dec(v_i_3064_);
v_stop_boxed_3068_ = lean_unbox_usize(v_stop_3065_);
lean_dec(v_stop_3065_);
v_res_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_3062_, v_as_3063_, v_i_boxed_3067_, v_stop_boxed_3068_, v_b_3066_);
lean_dec_ref(v_as_3063_);
lean_dec_ref(v_eqs_3062_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(lean_object* v_eqs_3072_, lean_object* v_as_3073_, lean_object* v_start_3074_, lean_object* v_stop_3075_){
_start:
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___closed__0));
v___x_3077_ = lean_nat_dec_lt(v_start_3074_, v_stop_3075_);
if (v___x_3077_ == 0)
{
return v___x_3076_;
}
else
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = lean_array_get_size(v_as_3073_);
v___x_3079_ = lean_nat_dec_le(v_stop_3075_, v___x_3078_);
if (v___x_3079_ == 0)
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_nat_dec_lt(v_start_3074_, v___x_3078_);
if (v___x_3080_ == 0)
{
return v___x_3076_;
}
else
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_usize_of_nat(v_start_3074_);
v___x_3082_ = lean_usize_of_nat(v___x_3078_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_3072_, v_as_3073_, v___x_3081_, v___x_3082_, v___x_3076_);
return v___x_3083_;
}
}
else
{
size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_usize_of_nat(v_start_3074_);
v___x_3085_ = lean_usize_of_nat(v_stop_3075_);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0_spec__0(v_eqs_3072_, v_as_3073_, v___x_3084_, v___x_3085_, v___x_3076_);
return v___x_3086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0___boxed(lean_object* v_eqs_3087_, lean_object* v_as_3088_, lean_object* v_start_3089_, lean_object* v_stop_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3087_, v_as_3088_, v_start_3089_, v_stop_3090_);
lean_dec(v_stop_3090_);
lean_dec(v_start_3089_);
lean_dec_ref(v_as_3088_);
lean_dec_ref(v_eqs_3087_);
return v_res_3091_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(lean_object* v_fvarId_3092_, lean_object* v_type_3093_, lean_object* v_deps_3094_, lean_object* v_eqs_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_eqs_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3101_ = lean_unsigned_to_nat(0u);
v___x_3102_ = lean_array_get_size(v_deps_3094_);
v_eqs_3103_ = l_Array_filterMapM___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__0(v_eqs_3095_, v_deps_3094_, v___x_3101_, v___x_3102_);
v___x_3104_ = lean_array_get_size(v_eqs_3103_);
v___x_3105_ = lean_nat_dec_eq(v___x_3104_, v___x_3101_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_type_3093_);
v___x_3107_ = 0;
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_Meta_mkFreshExprMVar(v___x_3106_, v___x_3107_, v___x_3108_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; size_t v_sz_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = l_Lean_Expr_mvarId_x21(v_a_3110_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v_sz_3114_ = lean_array_size(v_eqs_3103_);
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2(v___x_3104_, v_eqs_3103_, v_sz_3114_, v___x_3115_, v___x_3113_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec_ref(v_eqs_3103_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_fst_3118_; lean_object* v_snd_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_fst_3118_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_fst_3118_);
v_snd_3119_ = lean_ctor_get(v_a_3117_, 1);
lean_inc(v_snd_3119_);
lean_dec(v_a_3117_);
v___x_3120_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_getFVarId(v_snd_3119_, v_fvarId_3092_);
lean_dec(v_fvarId_3092_);
lean_dec(v_snd_3119_);
v___x_3121_ = l_Lean_mkFVar(v___x_3120_);
v___x_3122_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_fst_3118_, v___x_3121_, v_a_3097_);
lean_dec_ref(v___x_3122_);
v___x_3123_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_a_3110_, v_a_3097_);
return v___x_3123_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3110_);
lean_dec(v_fvarId_3092_);
v_a_3124_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3116_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3116_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_dec_ref(v_eqs_3103_);
lean_dec(v_fvarId_3092_);
return v___x_3109_;
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec_ref(v_eqs_3103_);
lean_dec_ref(v_type_3093_);
v___x_3132_ = l_Lean_mkFVar(v_fvarId_3092_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_3092_ = stack[0].m_obj;
lean_object* v_type_3093_ = stack[1].m_obj;
lean_object* v_deps_3094_ = stack[2].m_obj;
lean_object* v_eqs_3095_ = stack[3].m_obj;
lean_object* v_a_3096_ = stack[4].m_obj;
lean_object* v_a_3097_ = stack[5].m_obj;
lean_object* v_a_3098_ = stack[6].m_obj;
lean_object* v_a_3099_ = stack[7].m_obj;
lean_object* v_res_3134_;
v_res_3134_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3092_, v_type_3093_, v_deps_3094_, v_eqs_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
stack->m_obj
 = v_res_3134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast___boxed(lean_object* v_fvarId_3135_, lean_object* v_type_3136_, lean_object* v_deps_3137_, lean_object* v_eqs_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v_fvarId_3135_, v_type_3136_, v_deps_3137_, v_eqs_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_eqs_3138_);
lean_dec_ref(v_deps_3137_);
return v_res_3144_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(lean_object* v_mvarId_3145_, lean_object* v_val_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___redArg(v_mvarId_3145_, v_val_3146_, v___y_3148_);
return v___x_3152_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3145_ = stack[0].m_obj;
lean_object* v_val_3146_ = stack[1].m_obj;
lean_object* v___y_3147_ = stack[2].m_obj;
lean_object* v___y_3148_ = stack[3].m_obj;
lean_object* v___y_3149_ = stack[4].m_obj;
lean_object* v___y_3150_ = stack[5].m_obj;
lean_object* v_res_3153_;
v_res_3153_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3145_, v_val_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3___boxed(lean_object* v_mvarId_3154_, lean_object* v_val_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3(v_mvarId_3154_, v_val_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4(lean_object* v_00_u03b2_3162_, lean_object* v_x_3163_, lean_object* v_x_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4___redArg(v_x_3163_, v_x_3164_, v_x_3165_);
return v___x_3166_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3167_, lean_object* v_x_3168_, size_t v_x_3169_, size_t v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___redArg(v_x_3168_, v_x_3169_, v_x_3170_, v_x_3171_, v_x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3168_ = stack[1].m_obj;
size_t v_x_3169_ = stack[2].m_num;
size_t v_x_3170_ = stack[3].m_num;
lean_object* v_x_3171_ = stack[4].m_obj;
lean_object* v_x_3172_ = stack[5].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(lean_box(0), v_x_3168_, v_x_3169_, v_x_3170_, v_x_3171_, v_x_3172_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_x_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_){
_start:
{
size_t v_x_4898__boxed_3181_; size_t v_x_4899__boxed_3182_; lean_object* v_res_3183_; 
v_x_4898__boxed_3181_ = lean_unbox_usize(v_x_3177_);
lean_dec(v_x_3177_);
v_x_4899__boxed_3182_ = lean_unbox_usize(v_x_3178_);
lean_dec(v_x_3178_);
v_res_3183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6(v_00_u03b2_3175_, v_x_3176_, v_x_4898__boxed_3181_, v_x_4899__boxed_3182_, v_x_3179_, v_x_3180_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3184_, lean_object* v_n_3185_, lean_object* v_k_3186_, lean_object* v_v_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7___redArg(v_n_3185_, v_k_3186_, v_v_3187_);
return v___x_3188_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3189_, size_t v_depth_3190_, lean_object* v_keys_3191_, lean_object* v_vals_3192_, lean_object* v_heq_3193_, lean_object* v_i_3194_, lean_object* v_entries_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_3190_, v_keys_3191_, v_vals_3192_, v_i_3194_, v_entries_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3190_ = stack[1].m_num;
lean_object* v_keys_3191_ = stack[2].m_obj;
lean_object* v_vals_3192_ = stack[3].m_obj;
lean_object* v_i_3194_ = stack[5].m_obj;
lean_object* v_entries_3195_ = stack[6].m_obj;
lean_object* v_res_3197_;
v_res_3197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(lean_box(0), v_depth_3190_, v_keys_3191_, v_vals_3192_, lean_box(0), v_i_3194_, v_entries_3195_);
stack->m_obj
 = v_res_3197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_3198_, lean_object* v_depth_3199_, lean_object* v_keys_3200_, lean_object* v_vals_3201_, lean_object* v_heq_3202_, lean_object* v_i_3203_, lean_object* v_entries_3204_){
_start:
{
size_t v_depth_boxed_3205_; lean_object* v_res_3206_; 
v_depth_boxed_3205_ = lean_unbox_usize(v_depth_3199_);
lean_dec(v_depth_3199_);
v_res_3206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_3198_, v_depth_boxed_3205_, v_keys_3200_, v_vals_3201_, v_heq_3202_, v_i_3203_, v_entries_3204_);
lean_dec_ref(v_vals_3201_);
lean_dec_ref(v_keys_3200_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_3208_, v_x_3209_, v_x_3210_, v_x_3211_);
return v___x_3212_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(lean_object* v_msg_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___f_3220_; lean_object* v___x_1366__overap_3221_; lean_object* v___x_3222_; 
v___f_3220_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1366__overap_3221_ = lean_panic_fn_borrowed(v___f_3220_, v_msg_3214_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
v___x_3222_ = lean_apply_5(v___x_1366__overap_3221_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, lean_box(0));
return v___x_3222_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3214_ = stack[0].m_obj;
lean_object* v___y_3215_ = stack[1].m_obj;
lean_object* v___y_3216_ = stack[2].m_obj;
lean_object* v___y_3217_ = stack[3].m_obj;
lean_object* v___y_3218_ = stack[4].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
stack->m_obj
 = v_res_3223_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___boxed(lean_object* v_msg_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v_msg_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
return v_res_3230_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3234_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3235_ = lean_unsigned_to_nat(34u);
v___x_3236_ = lean_unsigned_to_nat(360u);
v___x_3237_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3238_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3239_ = l_mkPanicMessageWithDecl(v___x_3238_, v___x_3237_, v___x_3236_, v___x_3235_, v___x_3234_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed(lean_object* v___x_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v_i_3243_, lean_object* v_kinds_3244_, lean_object* v___x_3245_, lean_object* v_lhs_3246_, lean_object* v_rhs_3247_, lean_object* v_type_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v___x_1573__boxed_3254_; uint8_t v___x_1574__boxed_3255_; lean_object* v_res_3256_; 
v___x_1573__boxed_3254_ = lean_unbox(v___x_3241_);
v___x_1574__boxed_3255_ = lean_unbox(v___x_3242_);
v_res_3256_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3240_, v___x_1573__boxed_3254_, v___x_1574__boxed_3255_, v_i_3243_, v_kinds_3244_, v___x_3245_, v_lhs_3246_, v_rhs_3247_, v_type_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3256_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(lean_object* v___x_3257_, uint8_t v___x_3258_, uint8_t v___x_3259_, lean_object* v_i_3260_, lean_object* v___x_3261_, lean_object* v_kinds_3262_, lean_object* v_typeSub_3263_, lean_object* v_lhs_3264_, lean_object* v_rhs_3265_, lean_object* v_type_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
lean_inc_ref(v_rhs_3265_);
v___x_3272_ = lean_array_push(v___x_3257_, v_rhs_3265_);
v___x_3273_ = 1;
v___x_3274_ = l_Lean_Meta_mkLambdaFVars(v___x_3272_, v_type_3266_, v___x_3258_, v___x_3259_, v___x_3258_, v___x_3259_, v___x_3273_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v___x_3272_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = lean_nat_add(v_i_3260_, v___x_3261_);
v___x_3277_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3262_, v___x_3276_, v_typeSub_3263_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__2___closed__2));
v___x_3280_ = lean_unsigned_to_nat(2u);
v___x_3281_ = lean_mk_empty_array_with_capacity(v___x_3280_);
v___x_3282_ = lean_array_push(v___x_3281_, v_lhs_3264_);
v___x_3283_ = lean_array_push(v___x_3282_, v_rhs_3265_);
lean_inc_ref(v___x_3283_);
v___x_3284_ = l_Lean_Meta_mkAppM(v___x_3279_, v___x_3283_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_Meta_mkEqNDRec(v_a_3275_, v_a_3278_, v_a_3285_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = l_Lean_Meta_mkLambdaFVars(v___x_3283_, v_a_3287_, v___x_3258_, v___x_3259_, v___x_3258_, v___x_3259_, v___x_3273_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec_ref(v___x_3283_);
return v___x_3288_;
}
else
{
lean_dec_ref(v___x_3283_);
return v___x_3286_;
}
}
else
{
lean_dec_ref(v___x_3283_);
lean_dec(v_a_3278_);
lean_dec(v_a_3275_);
return v___x_3284_;
}
}
else
{
lean_dec(v_a_3275_);
lean_dec_ref(v_rhs_3265_);
lean_dec_ref(v_lhs_3264_);
return v___x_3277_;
}
}
else
{
lean_dec_ref(v_rhs_3265_);
lean_dec_ref(v_lhs_3264_);
lean_dec_ref(v_typeSub_3263_);
lean_dec_ref(v_kinds_3262_);
return v___x_3274_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3257_ = stack[0].m_obj;
uint8_t v___x_3258_ = stack[1].m_num;
uint8_t v___x_3259_ = stack[2].m_num;
lean_object* v_i_3260_ = stack[3].m_obj;
lean_object* v___x_3261_ = stack[4].m_obj;
lean_object* v_kinds_3262_ = stack[5].m_obj;
lean_object* v_typeSub_3263_ = stack[6].m_obj;
lean_object* v_lhs_3264_ = stack[7].m_obj;
lean_object* v_rhs_3265_ = stack[8].m_obj;
lean_object* v_type_3266_ = stack[9].m_obj;
lean_object* v___y_3267_ = stack[10].m_obj;
lean_object* v___y_3268_ = stack[11].m_obj;
lean_object* v___y_3269_ = stack[12].m_obj;
lean_object* v___y_3270_ = stack[13].m_obj;
lean_object* v_res_3289_;
v_res_3289_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3257_, v___x_3258_, v___x_3259_, v_i_3260_, v___x_3261_, v_kinds_3262_, v_typeSub_3263_, v_lhs_3264_, v_rhs_3265_, v_type_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
stack->m_obj
 = v_res_3289_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed(lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v___x_3292_, lean_object* v_i_3293_, lean_object* v___x_3294_, lean_object* v_kinds_3295_, lean_object* v_typeSub_3296_, lean_object* v_lhs_3297_, lean_object* v_rhs_3298_, lean_object* v_type_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v___x_1637__boxed_3305_; uint8_t v___x_1638__boxed_3306_; lean_object* v_res_3307_; 
v___x_1637__boxed_3305_ = lean_unbox(v___x_3291_);
v___x_1638__boxed_3306_ = lean_unbox(v___x_3292_);
v_res_3307_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2(v___x_3290_, v___x_1637__boxed_3305_, v___x_1638__boxed_3306_, v_i_3293_, v___x_3294_, v_kinds_3295_, v_typeSub_3296_, v_lhs_3297_, v_rhs_3298_, v_type_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___x_3294_);
lean_dec(v_i_3293_);
return v_res_3307_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(uint8_t v___x_3308_, lean_object* v_kinds_3309_, lean_object* v_i_3310_, uint8_t v___x_3311_, uint8_t v___x_3312_, lean_object* v_lhs_3313_, lean_object* v_type_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_box(v___x_3308_);
v___x_3324_ = lean_array_get(v___x_3323_, v_kinds_3309_, v_i_3310_);
lean_dec(v___x_3323_);
v___x_3325_ = lean_unbox(v___x_3324_);
lean_dec(v___x_3324_);
switch(v___x_3325_)
{
case 1:
{
lean_dec_ref(v_type_3314_);
lean_dec_ref(v_lhs_3313_);
lean_dec(v_i_3310_);
lean_dec_ref(v_kinds_3309_);
goto v___jp_3320_;
}
case 2:
{
lean_object* v___x_3326_; 
lean_inc_ref(v_lhs_3313_);
v___x_3326_ = l_Lean_Meta_mkEqRefl(v_lhs_3313_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___f_3337_; lean_object* v___x_3338_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l_Lean_Expr_bindingBody_x21(v_type_3314_);
v___x_3329_ = l_Lean_Expr_bindingBody_x21(v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(2u);
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_3330_);
lean_inc_ref(v___x_3331_);
v___x_3332_ = lean_array_push(v___x_3331_, v_a_3327_);
lean_inc_ref(v_lhs_3313_);
v___x_3333_ = lean_array_push(v___x_3332_, v_lhs_3313_);
v___x_3334_ = lean_expr_instantiate(v___x_3329_, v___x_3333_);
lean_dec_ref(v___x_3333_);
lean_dec_ref(v___x_3329_);
v___x_3335_ = lean_box(v___x_3311_);
v___x_3336_ = lean_box(v___x_3312_);
v___f_3337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_3337_, 0, v___x_3331_);
lean_closure_set(v___f_3337_, 1, v___x_3335_);
lean_closure_set(v___f_3337_, 2, v___x_3336_);
lean_closure_set(v___f_3337_, 3, v_i_3310_);
lean_closure_set(v___f_3337_, 4, v_kinds_3309_);
lean_closure_set(v___f_3337_, 5, v___x_3334_);
lean_closure_set(v___f_3337_, 6, v_lhs_3313_);
v___x_3338_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3314_, v___f_3337_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
return v___x_3338_;
}
else
{
lean_dec_ref(v_type_3314_);
lean_dec_ref(v_lhs_3313_);
lean_dec(v_i_3310_);
lean_dec_ref(v_kinds_3309_);
return v___x_3326_;
}
}
case 4:
{
lean_dec_ref(v_type_3314_);
lean_dec_ref(v_lhs_3313_);
lean_dec(v_i_3310_);
lean_dec_ref(v_kinds_3309_);
goto v___jp_3320_;
}
case 5:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v_typeSub_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; 
v___x_3339_ = l_Lean_Expr_bindingBody_x21(v_type_3314_);
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_3340_);
lean_inc_ref(v_lhs_3313_);
lean_inc_ref(v___x_3341_);
v___x_3342_ = lean_array_push(v___x_3341_, v_lhs_3313_);
v_typeSub_3343_ = lean_expr_instantiate(v___x_3339_, v___x_3342_);
lean_dec_ref(v___x_3342_);
lean_dec_ref(v___x_3339_);
v___x_3344_ = lean_box(v___x_3311_);
v___x_3345_ = lean_box(v___x_3312_);
v___f_3346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__2___boxed), 15, 8);
lean_closure_set(v___f_3346_, 0, v___x_3341_);
lean_closure_set(v___f_3346_, 1, v___x_3344_);
lean_closure_set(v___f_3346_, 2, v___x_3345_);
lean_closure_set(v___f_3346_, 3, v_i_3310_);
lean_closure_set(v___f_3346_, 4, v___x_3340_);
lean_closure_set(v___f_3346_, 5, v_kinds_3309_);
lean_closure_set(v___f_3346_, 6, v_typeSub_3343_);
lean_closure_set(v___f_3346_, 7, v_lhs_3313_);
v___x_3347_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3314_, v___f_3346_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
return v___x_3347_;
}
default: 
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_nat_add(v_i_3310_, v___x_3348_);
lean_dec(v_i_3310_);
v___x_3350_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3309_, v___x_3349_, v_type_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = lean_mk_empty_array_with_capacity(v___x_3348_);
v___x_3353_ = lean_array_push(v___x_3352_, v_lhs_3313_);
v___x_3354_ = 1;
v___x_3355_ = l_Lean_Meta_mkLambdaFVars(v___x_3353_, v_a_3351_, v___x_3311_, v___x_3312_, v___x_3311_, v___x_3312_, v___x_3354_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec_ref(v___x_3353_);
return v___x_3355_;
}
else
{
lean_dec_ref(v_lhs_3313_);
return v___x_3350_;
}
}
}
v___jp_3320_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___closed__0);
v___x_3322_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3321_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
return v___x_3322_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3308_ = stack[0].m_num;
lean_object* v_kinds_3309_ = stack[1].m_obj;
lean_object* v_i_3310_ = stack[2].m_obj;
uint8_t v___x_3311_ = stack[3].m_num;
uint8_t v___x_3312_ = stack[4].m_num;
lean_object* v_lhs_3313_ = stack[5].m_obj;
lean_object* v_type_3314_ = stack[6].m_obj;
lean_object* v___y_3315_ = stack[7].m_obj;
lean_object* v___y_3316_ = stack[8].m_obj;
lean_object* v___y_3317_ = stack[9].m_obj;
lean_object* v___y_3318_ = stack[10].m_obj;
lean_object* v_res_3356_;
v_res_3356_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v___x_3308_, v_kinds_3309_, v_i_3310_, v___x_3311_, v___x_3312_, v_lhs_3313_, v_type_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
stack->m_obj
 = v_res_3356_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed(lean_object* v___x_3357_, lean_object* v_kinds_3358_, lean_object* v_i_3359_, lean_object* v___x_3360_, lean_object* v___x_3361_, lean_object* v_lhs_3362_, lean_object* v_type_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
uint8_t v___x_1674__boxed_3369_; uint8_t v___x_1675__boxed_3370_; uint8_t v___x_1676__boxed_3371_; lean_object* v_res_3372_; 
v___x_1674__boxed_3369_ = lean_unbox(v___x_3357_);
v___x_1675__boxed_3370_ = lean_unbox(v___x_3360_);
v___x_1676__boxed_3371_ = lean_unbox(v___x_3361_);
v_res_3372_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3(v___x_1674__boxed_3369_, v_kinds_3358_, v_i_3359_, v___x_1675__boxed_3370_, v___x_1676__boxed_3371_, v_lhs_3362_, v_type_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3372_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3374_ = lean_unsigned_to_nat(43u);
v___x_3375_ = lean_unsigned_to_nat(355u);
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__1));
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3378_ = l_mkPanicMessageWithDecl(v___x_3377_, v___x_3376_, v___x_3375_, v___x_3374_, v___x_3373_);
return v___x_3378_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(lean_object* v_kinds_3379_, lean_object* v_i_3380_, lean_object* v_type_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_array_get_size(v_kinds_3379_);
v___x_3388_ = lean_nat_dec_eq(v_i_3380_, v___x_3387_);
if (v___x_3388_ == 0)
{
uint8_t v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; 
v___x_3389_ = 0;
v___x_3390_ = 1;
v___x_3391_ = lean_box(v___x_3389_);
v___x_3392_ = lean_box(v___x_3388_);
v___x_3393_ = lean_box(v___x_3390_);
v___f_3394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__3___boxed), 12, 5);
lean_closure_set(v___f_3394_, 0, v___x_3391_);
lean_closure_set(v___f_3394_, 1, v_kinds_3379_);
lean_closure_set(v___f_3394_, 2, v_i_3380_);
lean_closure_set(v___f_3394_, 3, v___x_3392_);
lean_closure_set(v___f_3394_, 4, v___x_3393_);
v___x_3395_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3381_, v___f_3394_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
lean_dec(v_i_3380_);
lean_dec_ref(v_kinds_3379_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof___closed__1));
v___x_3397_ = lean_unsigned_to_nat(3u);
v___x_3398_ = l_Lean_Expr_isAppOfArity(v_type_3381_, v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v_type_3381_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__3);
v___x_3400_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0(v___x_3399_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = l_Lean_Expr_appFn_x21(v_type_3381_);
lean_dec_ref(v_type_3381_);
v___x_3402_ = l_Lean_Expr_appArg_x21(v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = l_Lean_Meta_mkEqRefl(v___x_3402_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_kinds_3379_ = stack[0].m_obj;
lean_object* v_i_3380_ = stack[1].m_obj;
lean_object* v_type_3381_ = stack[2].m_obj;
lean_object* v_a_3382_ = stack[3].m_obj;
lean_object* v_a_3383_ = stack[4].m_obj;
lean_object* v_a_3384_ = stack[5].m_obj;
lean_object* v_a_3385_ = stack[6].m_obj;
lean_object* v_res_3404_;
v_res_3404_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3379_, v_i_3380_, v_type_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
stack->m_obj
 = v_res_3404_;
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(lean_object* v___x_3405_, lean_object* v_rhs_3406_, uint8_t v___x_3407_, uint8_t v___x_3408_, lean_object* v_i_3409_, lean_object* v_kinds_3410_, lean_object* v___x_3411_, lean_object* v_lhs_3412_, lean_object* v_heq_3413_, lean_object* v_type_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; 
lean_inc_ref(v_rhs_3406_);
v___x_3420_ = lean_array_push(v___x_3405_, v_rhs_3406_);
lean_inc_ref(v_heq_3413_);
v___x_3421_ = lean_array_push(v___x_3420_, v_heq_3413_);
v___x_3422_ = 1;
v___x_3423_ = l_Lean_Meta_mkLambdaFVars(v___x_3421_, v_type_3414_, v___x_3407_, v___x_3408_, v___x_3407_, v___x_3408_, v___x_3422_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec_ref(v___x_3421_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_add(v_i_3409_, v___x_3425_);
v___x_3427_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3410_, v___x_3426_, v___x_3411_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
lean_inc_ref(v_heq_3413_);
v___x_3429_ = l_Lean_Meta_mkEqRec(v_a_3424_, v_a_3428_, v_heq_3413_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___x_3431_ = lean_unsigned_to_nat(3u);
v___x_3432_ = lean_mk_empty_array_with_capacity(v___x_3431_);
v___x_3433_ = lean_array_push(v___x_3432_, v_lhs_3412_);
v___x_3434_ = lean_array_push(v___x_3433_, v_rhs_3406_);
v___x_3435_ = lean_array_push(v___x_3434_, v_heq_3413_);
v___x_3436_ = l_Lean_Meta_mkLambdaFVars(v___x_3435_, v_a_3430_, v___x_3407_, v___x_3408_, v___x_3407_, v___x_3408_, v___x_3422_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec_ref(v___x_3435_);
return v___x_3436_;
}
else
{
lean_dec_ref(v_heq_3413_);
lean_dec_ref(v_lhs_3412_);
lean_dec_ref(v_rhs_3406_);
return v___x_3429_;
}
}
else
{
lean_dec(v_a_3424_);
lean_dec_ref(v_heq_3413_);
lean_dec_ref(v_lhs_3412_);
lean_dec_ref(v_rhs_3406_);
return v___x_3427_;
}
}
else
{
lean_dec_ref(v_heq_3413_);
lean_dec_ref(v_lhs_3412_);
lean_dec_ref(v___x_3411_);
lean_dec_ref(v_kinds_3410_);
lean_dec_ref(v_rhs_3406_);
return v___x_3423_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3405_ = stack[0].m_obj;
lean_object* v_rhs_3406_ = stack[1].m_obj;
uint8_t v___x_3407_ = stack[2].m_num;
uint8_t v___x_3408_ = stack[3].m_num;
lean_object* v_i_3409_ = stack[4].m_obj;
lean_object* v_kinds_3410_ = stack[5].m_obj;
lean_object* v___x_3411_ = stack[6].m_obj;
lean_object* v_lhs_3412_ = stack[7].m_obj;
lean_object* v_heq_3413_ = stack[8].m_obj;
lean_object* v_type_3414_ = stack[9].m_obj;
lean_object* v___y_3415_ = stack[10].m_obj;
lean_object* v___y_3416_ = stack[11].m_obj;
lean_object* v___y_3417_ = stack[12].m_obj;
lean_object* v___y_3418_ = stack[13].m_obj;
lean_object* v_res_3437_;
v_res_3437_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3405_, v_rhs_3406_, v___x_3407_, v___x_3408_, v_i_3409_, v_kinds_3410_, v___x_3411_, v_lhs_3412_, v_heq_3413_, v_type_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
stack->m_obj
 = v_res_3437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed(lean_object* v___x_3438_, lean_object* v_rhs_3439_, lean_object* v___x_3440_, lean_object* v___x_3441_, lean_object* v_i_3442_, lean_object* v_kinds_3443_, lean_object* v___x_3444_, lean_object* v_lhs_3445_, lean_object* v_heq_3446_, lean_object* v_type_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v___x_1584__boxed_3453_; uint8_t v___x_1585__boxed_3454_; lean_object* v_res_3455_; 
v___x_1584__boxed_3453_ = lean_unbox(v___x_3440_);
v___x_1585__boxed_3454_ = lean_unbox(v___x_3441_);
v_res_3455_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0(v___x_3438_, v_rhs_3439_, v___x_1584__boxed_3453_, v___x_1585__boxed_3454_, v_i_3442_, v_kinds_3443_, v___x_3444_, v_lhs_3445_, v_heq_3446_, v_type_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v_i_3442_);
return v_res_3455_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(lean_object* v___x_3456_, uint8_t v___x_3457_, uint8_t v___x_3458_, lean_object* v_i_3459_, lean_object* v_kinds_3460_, lean_object* v___x_3461_, lean_object* v_lhs_3462_, lean_object* v_rhs_3463_, lean_object* v_type_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; 
v___x_3470_ = lean_box(v___x_3457_);
v___x_3471_ = lean_box(v___x_3458_);
v___f_3472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3472_, 0, v___x_3456_);
lean_closure_set(v___f_3472_, 1, v_rhs_3463_);
lean_closure_set(v___f_3472_, 2, v___x_3470_);
lean_closure_set(v___f_3472_, 3, v___x_3471_);
lean_closure_set(v___f_3472_, 4, v_i_3459_);
lean_closure_set(v___f_3472_, 5, v_kinds_3460_);
lean_closure_set(v___f_3472_, 6, v___x_3461_);
lean_closure_set(v___f_3472_, 7, v_lhs_3462_);
v___x_3473_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_withNext___redArg(v_type_3464_, v___f_3472_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3473_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3456_ = stack[0].m_obj;
uint8_t v___x_3457_ = stack[1].m_num;
uint8_t v___x_3458_ = stack[2].m_num;
lean_object* v_i_3459_ = stack[3].m_obj;
lean_object* v_kinds_3460_ = stack[4].m_obj;
lean_object* v___x_3461_ = stack[5].m_obj;
lean_object* v_lhs_3462_ = stack[6].m_obj;
lean_object* v_rhs_3463_ = stack[7].m_obj;
lean_object* v_type_3464_ = stack[8].m_obj;
lean_object* v___y_3465_ = stack[9].m_obj;
lean_object* v___y_3466_ = stack[10].m_obj;
lean_object* v___y_3467_ = stack[11].m_obj;
lean_object* v___y_3468_ = stack[12].m_obj;
lean_object* v_res_3474_;
v_res_3474_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___lam__1(v___x_3456_, v___x_3457_, v___x_3458_, v_i_3459_, v_kinds_3460_, v___x_3461_, v_lhs_3462_, v_rhs_3463_, v_type_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
stack->m_obj
 = v_res_3474_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___boxed(lean_object* v_kinds_3475_, lean_object* v_i_3476_, lean_object* v_type_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3475_, v_i_3476_, v_type_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3483_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(lean_object* v_type_3484_, lean_object* v_kinds_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go(v_kinds_3485_, v___x_3491_, v_type_3484_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
return v___x_3492_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3484_ = stack[0].m_obj;
lean_object* v_kinds_3485_ = stack[1].m_obj;
lean_object* v_a_3486_ = stack[2].m_obj;
lean_object* v_a_3487_ = stack[3].m_obj;
lean_object* v_a_3488_ = stack[4].m_obj;
lean_object* v_a_3489_ = stack[5].m_obj;
lean_object* v_res_3493_;
v_res_3493_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3484_, v_kinds_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
stack->m_obj
 = v_res_3493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof___boxed(lean_object* v_type_3494_, lean_object* v_kinds_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_type_3494_, v_kinds_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
return v_res_3501_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(lean_object* v_msg_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___f_3508_; lean_object* v___x_1532__overap_3509_; lean_object* v___x_3510_; 
v___f_3508_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1532__overap_3509_ = lean_panic_fn_borrowed(v___f_3508_, v_msg_3502_);
lean_inc(v___y_3506_);
lean_inc_ref(v___y_3505_);
lean_inc(v___y_3504_);
lean_inc_ref(v___y_3503_);
v___x_3510_ = lean_apply_5(v___x_1532__overap_3509_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, lean_box(0));
return v___x_3510_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3502_ = stack[0].m_obj;
lean_object* v___y_3503_ = stack[1].m_obj;
lean_object* v___y_3504_ = stack[2].m_obj;
lean_object* v___y_3505_ = stack[3].m_obj;
lean_object* v___y_3506_ = stack[4].m_obj;
lean_object* v_res_3511_;
v_res_3511_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_msg_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
stack->m_obj
 = v_res_3511_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0___boxed(lean_object* v_msg_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3518_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(lean_object* v_bs_3519_, lean_object* v_k_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3519_, v_k_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_a_3535_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3526_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3526_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_3519_ = stack[0].m_obj;
lean_object* v_k_3520_ = stack[1].m_obj;
lean_object* v___y_3521_ = stack[2].m_obj;
lean_object* v___y_3522_ = stack[3].m_obj;
lean_object* v___y_3523_ = stack[4].m_obj;
lean_object* v___y_3524_ = stack[5].m_obj;
lean_object* v_res_3543_;
v_res_3543_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3519_, v_k_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
stack->m_obj
 = v_res_3543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg___boxed(lean_object* v_bs_3544_, lean_object* v_k_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3544_, v_k_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v_bs_3544_);
return v_res_3551_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_object* v_00_u03b1_3552_, lean_object* v_bs_3553_, lean_object* v_k_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v_bs_3553_, v_k_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_3553_ = stack[1].m_obj;
lean_object* v_k_3554_ = stack[2].m_obj;
lean_object* v___y_3555_ = stack[3].m_obj;
lean_object* v___y_3556_ = stack[4].m_obj;
lean_object* v___y_3557_ = stack[5].m_obj;
lean_object* v___y_3558_ = stack[6].m_obj;
lean_object* v_res_3561_;
v_res_3561_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(lean_box(0), v_bs_3553_, v_k_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
stack->m_obj
 = v_res_3561_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3562_, lean_object* v_bs_3563_, lean_object* v_k_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2(v_00_u03b1_3562_, v_bs_3563_, v_k_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_bs_3563_);
return v_res_3570_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_bs_3573_){
_start:
{
uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3572_, v_sz_3571_);
if (v___x_3574_ == 0)
{
return v_bs_3573_;
}
else
{
lean_object* v_v_3575_; lean_object* v___x_3576_; lean_object* v_bs_x27_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v_v_3575_ = lean_array_uget(v_bs_3573_, v_i_3572_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v_bs_x27_3577_ = lean_array_uset(v_bs_3573_, v_i_3572_, v___x_3576_);
v___x_3578_ = l_Lean_Expr_fvarId_x21(v_v_3575_);
lean_dec(v_v_3575_);
v___x_3579_ = 1;
v___x_3580_ = lean_box(v___x_3579_);
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3578_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = ((size_t)1ULL);
v___x_3583_ = lean_usize_add(v_i_3572_, v___x_3582_);
v___x_3584_ = lean_array_uset(v_bs_x27_3577_, v_i_3572_, v___x_3581_);
v_i_3572_ = v___x_3583_;
v_bs_3573_ = v___x_3584_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3571_ = stack[0].m_num;
size_t v_i_3572_ = stack[1].m_num;
lean_object* v_bs_3573_ = stack[2].m_obj;
lean_object* v_res_3586_;
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_3571_, v_i_3572_, v_bs_3573_);
stack->m_obj
 = v_res_3586_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1___boxed(lean_object* v_sz_3587_, lean_object* v_i_3588_, lean_object* v_bs_3589_){
_start:
{
size_t v_sz_boxed_3590_; size_t v_i_boxed_3591_; lean_object* v_res_3592_; 
v_sz_boxed_3590_ = lean_unbox_usize(v_sz_3587_);
lean_dec(v_sz_3587_);
v_i_boxed_3591_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_boxed_3590_, v_i_boxed_3591_, v_bs_3589_);
return v_res_3592_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(lean_object* v_bs_3593_, lean_object* v_k_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
size_t v_sz_3600_; size_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_sz_3600_ = lean_array_size(v_bs_3593_);
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__1(v_sz_3600_, v___x_3601_, v_bs_3593_);
v___x_3603_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_spec__2___redArg(v___x_3602_, v_k_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec_ref(v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_3593_ = stack[0].m_obj;
lean_object* v_k_3594_ = stack[1].m_obj;
lean_object* v___y_3595_ = stack[2].m_obj;
lean_object* v___y_3596_ = stack[3].m_obj;
lean_object* v___y_3597_ = stack[4].m_obj;
lean_object* v___y_3598_ = stack[5].m_obj;
lean_object* v_res_3604_;
v_res_3604_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3593_, v_k_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
stack->m_obj
 = v_res_3604_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg___boxed(lean_object* v_bs_3605_, lean_object* v_k_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3605_, v_k_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
return v_res_3612_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_object* v_00_u03b1_3613_, lean_object* v_bs_3614_, lean_object* v_k_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v_bs_3614_, v_k_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_3614_ = stack[1].m_obj;
lean_object* v_k_3615_ = stack[2].m_obj;
lean_object* v___y_3616_ = stack[3].m_obj;
lean_object* v___y_3617_ = stack[4].m_obj;
lean_object* v___y_3618_ = stack[5].m_obj;
lean_object* v___y_3619_ = stack[6].m_obj;
lean_object* v_res_3622_;
v_res_3622_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(lean_box(0), v_bs_3614_, v_k_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
stack->m_obj
 = v_res_3622_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___boxed(lean_object* v_00_u03b1_3623_, lean_object* v_bs_3624_, lean_object* v_k_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1(v_00_u03b1_3623_, v_bs_3624_, v_k_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3631_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_3634_ = lean_unsigned_to_nat(38u);
v___x_3635_ = lean_unsigned_to_nat(328u);
v___x_3636_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__0));
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_3638_ = l_mkPanicMessageWithDecl(v___x_3637_, v___x_3636_, v___x_3635_, v___x_3634_, v___x_3633_);
return v___x_3638_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(lean_object* v_i_3639_, lean_object* v_rhss_3640_, lean_object* v_b_3641_, lean_object* v_eqs_3642_, lean_object* v_hyps_3643_, uint8_t v_subsingletonInstImplicitRhs_3644_, lean_object* v_f_3645_, lean_object* v_info_3646_, lean_object* v_kinds_3647_, lean_object* v_lhss_3648_, lean_object* v_eq_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_nat_add(v_i_3639_, v___x_3655_);
lean_inc_ref(v_b_3641_);
v___x_3657_ = lean_array_push(v_rhss_3640_, v_b_3641_);
v___x_3658_ = l_Lean_Expr_fvarId_x21(v_eq_3649_);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
v___x_3661_ = lean_array_push(v_eqs_3642_, v___x_3660_);
v___x_3662_ = lean_array_push(v_hyps_3643_, v_b_3641_);
v___x_3663_ = lean_array_push(v___x_3662_, v_eq_3649_);
v___x_3664_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3644_, v_f_3645_, v_info_3646_, v_kinds_3647_, v_lhss_3648_, v___x_3656_, v___x_3657_, v___x_3661_, v___x_3663_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3664_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3639_ = stack[0].m_obj;
lean_object* v_rhss_3640_ = stack[1].m_obj;
lean_object* v_b_3641_ = stack[2].m_obj;
lean_object* v_eqs_3642_ = stack[3].m_obj;
lean_object* v_hyps_3643_ = stack[4].m_obj;
uint8_t v_subsingletonInstImplicitRhs_3644_ = stack[5].m_num;
lean_object* v_f_3645_ = stack[6].m_obj;
lean_object* v_info_3646_ = stack[7].m_obj;
lean_object* v_kinds_3647_ = stack[8].m_obj;
lean_object* v_lhss_3648_ = stack[9].m_obj;
lean_object* v_eq_3649_ = stack[10].m_obj;
lean_object* v___y_3650_ = stack[11].m_obj;
lean_object* v___y_3651_ = stack[12].m_obj;
lean_object* v___y_3652_ = stack[13].m_obj;
lean_object* v___y_3653_ = stack[14].m_obj;
lean_object* v_res_3665_;
v_res_3665_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3639_, v_rhss_3640_, v_b_3641_, v_eqs_3642_, v_hyps_3643_, v_subsingletonInstImplicitRhs_3644_, v_f_3645_, v_info_3646_, v_kinds_3647_, v_lhss_3648_, v_eq_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
stack->m_obj
 = v_res_3665_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed(lean_object* v_i_3666_, lean_object* v_rhss_3667_, lean_object* v_b_3668_, lean_object* v_eqs_3669_, lean_object* v_hyps_3670_, lean_object* v_subsingletonInstImplicitRhs_3671_, lean_object* v_f_3672_, lean_object* v_info_3673_, lean_object* v_kinds_3674_, lean_object* v_lhss_3675_, lean_object* v_eq_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3682_; lean_object* v_res_3683_; 
v_subsingletonInstImplicitRhs_boxed_3682_ = lean_unbox(v_subsingletonInstImplicitRhs_3671_);
v_res_3683_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0(v_i_3666_, v_rhss_3667_, v_b_3668_, v_eqs_3669_, v_hyps_3670_, v_subsingletonInstImplicitRhs_boxed_3682_, v_f_3672_, v_info_3673_, v_kinds_3674_, v_lhss_3675_, v_eq_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v_i_3666_);
return v_res_3683_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(lean_object* v_i_3685_, lean_object* v_rhss_3686_, lean_object* v_eqs_3687_, lean_object* v_hyps_3688_, uint8_t v_subsingletonInstImplicitRhs_3689_, lean_object* v_f_3690_, lean_object* v_info_3691_, lean_object* v_kinds_3692_, lean_object* v_lhss_3693_, lean_object* v_lhs_3694_, lean_object* v___x_3695_, lean_object* v_b_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; lean_object* v___f_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_box(v_subsingletonInstImplicitRhs_3689_);
lean_inc_ref(v_b_3696_);
v___f_3703_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__0___boxed), 16, 10);
lean_closure_set(v___f_3703_, 0, v_i_3685_);
lean_closure_set(v___f_3703_, 1, v_rhss_3686_);
lean_closure_set(v___f_3703_, 2, v_b_3696_);
lean_closure_set(v___f_3703_, 3, v_eqs_3687_);
lean_closure_set(v___f_3703_, 4, v_hyps_3688_);
lean_closure_set(v___f_3703_, 5, v___x_3702_);
lean_closure_set(v___f_3703_, 6, v_f_3690_);
lean_closure_set(v___f_3703_, 7, v_info_3691_);
lean_closure_set(v___f_3703_, 8, v_kinds_3692_);
lean_closure_set(v___f_3703_, 9, v_lhss_3693_);
v___x_3704_ = l_Lean_Meta_mkEq(v_lhs_3694_, v_b_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___closed__0));
v___x_3707_ = l_Lean_Name_appendBefore(v___x_3695_, v___x_3706_);
v___x_3708_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0___redArg(v___x_3707_, v_a_3705_, v___f_3703_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3708_;
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v___f_3703_);
lean_dec(v___x_3695_);
v_a_3709_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3704_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3704_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3685_ = stack[0].m_obj;
lean_object* v_rhss_3686_ = stack[1].m_obj;
lean_object* v_eqs_3687_ = stack[2].m_obj;
lean_object* v_hyps_3688_ = stack[3].m_obj;
uint8_t v_subsingletonInstImplicitRhs_3689_ = stack[4].m_num;
lean_object* v_f_3690_ = stack[5].m_obj;
lean_object* v_info_3691_ = stack[6].m_obj;
lean_object* v_kinds_3692_ = stack[7].m_obj;
lean_object* v_lhss_3693_ = stack[8].m_obj;
lean_object* v_lhs_3694_ = stack[9].m_obj;
lean_object* v___x_3695_ = stack[10].m_obj;
lean_object* v_b_3696_ = stack[11].m_obj;
lean_object* v___y_3697_ = stack[12].m_obj;
lean_object* v___y_3698_ = stack[13].m_obj;
lean_object* v___y_3699_ = stack[14].m_obj;
lean_object* v___y_3700_ = stack[15].m_obj;
lean_object* v_res_3717_;
v_res_3717_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(v_i_3685_, v_rhss_3686_, v_eqs_3687_, v_hyps_3688_, v_subsingletonInstImplicitRhs_3689_, v_f_3690_, v_info_3691_, v_kinds_3692_, v_lhss_3693_, v_lhs_3694_, v___x_3695_, v_b_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
stack->m_obj
 = v_res_3717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed(lean_object** _args){
lean_object* v_i_3718_ = _args[0];
lean_object* v_rhss_3719_ = _args[1];
lean_object* v_eqs_3720_ = _args[2];
lean_object* v_hyps_3721_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_3722_ = _args[4];
lean_object* v_f_3723_ = _args[5];
lean_object* v_info_3724_ = _args[6];
lean_object* v_kinds_3725_ = _args[7];
lean_object* v_lhss_3726_ = _args[8];
lean_object* v_lhs_3727_ = _args[9];
lean_object* v___x_3728_ = _args[10];
lean_object* v_b_3729_ = _args[11];
lean_object* v___y_3730_ = _args[12];
lean_object* v___y_3731_ = _args[13];
lean_object* v___y_3732_ = _args[14];
lean_object* v___y_3733_ = _args[15];
lean_object* v___y_3734_ = _args[16];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3735_; lean_object* v_res_3736_; 
v_subsingletonInstImplicitRhs_boxed_3735_ = lean_unbox(v_subsingletonInstImplicitRhs_3722_);
v_res_3736_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1(v_i_3718_, v_rhss_3719_, v_eqs_3720_, v_hyps_3721_, v_subsingletonInstImplicitRhs_boxed_3735_, v_f_3723_, v_info_3724_, v_kinds_3725_, v_lhss_3726_, v_lhs_3727_, v___x_3728_, v_b_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
return v_res_3736_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(lean_object* v_i_3737_, lean_object* v_rhss_3738_, lean_object* v_eqs_3739_, lean_object* v_hyps_3740_, uint8_t v_subsingletonInstImplicitRhs_3741_, lean_object* v_f_3742_, lean_object* v_info_3743_, lean_object* v_kinds_3744_, lean_object* v_lhss_3745_, lean_object* v_lhs_3746_, lean_object* v___x_3747_, lean_object* v_name_3748_, uint8_t v_bi_3749_, lean_object* v_type_3750_, uint8_t v_kind_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; lean_object* v___f_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_box(v_subsingletonInstImplicitRhs_3741_);
v___f_3758_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___lam__1___boxed), 17, 11);
lean_closure_set(v___f_3758_, 0, v_i_3737_);
lean_closure_set(v___f_3758_, 1, v_rhss_3738_);
lean_closure_set(v___f_3758_, 2, v_eqs_3739_);
lean_closure_set(v___f_3758_, 3, v_hyps_3740_);
lean_closure_set(v___f_3758_, 4, v___x_3757_);
lean_closure_set(v___f_3758_, 5, v_f_3742_);
lean_closure_set(v___f_3758_, 6, v_info_3743_);
lean_closure_set(v___f_3758_, 7, v_kinds_3744_);
lean_closure_set(v___f_3758_, 8, v_lhss_3745_);
lean_closure_set(v___f_3758_, 9, v_lhs_3746_);
lean_closure_set(v___f_3758_, 10, v___x_3747_);
v___x_3759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3748_, v_bi_3749_, v_type_3750_, v___f_3758_, v_kind_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
v_a_3768_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3759_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3759_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3737_ = stack[0].m_obj;
lean_object* v_rhss_3738_ = stack[1].m_obj;
lean_object* v_eqs_3739_ = stack[2].m_obj;
lean_object* v_hyps_3740_ = stack[3].m_obj;
uint8_t v_subsingletonInstImplicitRhs_3741_ = stack[4].m_num;
lean_object* v_f_3742_ = stack[5].m_obj;
lean_object* v_info_3743_ = stack[6].m_obj;
lean_object* v_kinds_3744_ = stack[7].m_obj;
lean_object* v_lhss_3745_ = stack[8].m_obj;
lean_object* v_lhs_3746_ = stack[9].m_obj;
lean_object* v___x_3747_ = stack[10].m_obj;
lean_object* v_name_3748_ = stack[11].m_obj;
uint8_t v_bi_3749_ = stack[12].m_num;
lean_object* v_type_3750_ = stack[13].m_obj;
uint8_t v_kind_3751_ = stack[14].m_num;
lean_object* v___y_3752_ = stack[15].m_obj;
lean_object* v___y_3753_ = stack[16].m_obj;
lean_object* v___y_3754_ = stack[17].m_obj;
lean_object* v___y_3755_ = stack[18].m_obj;
lean_object* v_res_3776_;
v_res_3776_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3737_, v_rhss_3738_, v_eqs_3739_, v_hyps_3740_, v_subsingletonInstImplicitRhs_3741_, v_f_3742_, v_info_3743_, v_kinds_3744_, v_lhss_3745_, v_lhs_3746_, v___x_3747_, v_name_3748_, v_bi_3749_, v_type_3750_, v_kind_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
stack->m_obj
 = v_res_3776_;
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(lean_object* v_lhs_3777_, lean_object* v_rhss_3778_, lean_object* v_lhss_3779_, lean_object* v_i_3780_, lean_object* v_eqs_3781_, lean_object* v_hyps_3782_, uint8_t v_subsingletonInstImplicitRhs_3783_, lean_object* v_f_3784_, lean_object* v_info_3785_, lean_object* v_kinds_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc_ref(v_lhs_3777_);
v___x_3792_ = lean_infer_type(v_lhs_3777_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___y_3800_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = lean_array_get_size(v_rhss_3778_);
v___x_3795_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3779_);
v___x_3796_ = l_Array_toSubarray___redArg(v_lhss_3779_, v___x_3795_, v___x_3794_);
v___x_3797_ = l_Subarray_copy___redArg(v___x_3796_);
v___x_3798_ = l_Lean_Expr_replaceFVars(v_a_3793_, v___x_3797_, v_rhss_3778_);
lean_dec_ref(v___x_3797_);
lean_dec(v_a_3793_);
if (v_subsingletonInstImplicitRhs_3783_ == 0)
{
uint8_t v___x_3815_; 
v___x_3815_ = 1;
v___y_3800_ = v___x_3815_;
goto v___jp_3799_;
}
else
{
uint8_t v___x_3816_; 
v___x_3816_ = 3;
v___y_3800_ = v___x_3816_;
goto v___jp_3799_;
}
v___jp_3799_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = l_Lean_Expr_fvarId_x21(v_lhs_3777_);
v___x_3802_ = l_Lean_FVarId_getDecl___redArg(v___x_3801_, v___y_3787_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v___x_3804_ = l_Lean_LocalDecl_userName(v_a_3803_);
lean_dec(v_a_3803_);
v___x_3805_ = 0;
v___x_3806_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_3780_, v_rhss_3778_, v_lhs_3777_, v_eqs_3781_, v_hyps_3782_, v_subsingletonInstImplicitRhs_3783_, v_f_3784_, v_info_3785_, v_kinds_3786_, v_lhss_3779_, v___x_3804_, v___y_3800_, v___x_3798_, v___x_3805_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v___x_3806_;
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v___x_3798_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v_kinds_3786_);
lean_dec_ref(v_info_3785_);
lean_dec_ref(v_f_3784_);
lean_dec_ref(v_hyps_3782_);
lean_dec_ref(v_eqs_3781_);
lean_dec(v_i_3780_);
lean_dec_ref(v_lhss_3779_);
lean_dec_ref(v_rhss_3778_);
lean_dec_ref(v_lhs_3777_);
v_a_3807_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3802_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3802_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v_kinds_3786_);
lean_dec_ref(v_info_3785_);
lean_dec_ref(v_f_3784_);
lean_dec_ref(v_hyps_3782_);
lean_dec_ref(v_eqs_3781_);
lean_dec(v_i_3780_);
lean_dec_ref(v_lhss_3779_);
lean_dec_ref(v_rhss_3778_);
lean_dec_ref(v_lhs_3777_);
v_a_3817_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3792_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3792_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_3777_ = stack[0].m_obj;
lean_object* v_rhss_3778_ = stack[1].m_obj;
lean_object* v_lhss_3779_ = stack[2].m_obj;
lean_object* v_i_3780_ = stack[3].m_obj;
lean_object* v_eqs_3781_ = stack[4].m_obj;
lean_object* v_hyps_3782_ = stack[5].m_obj;
uint8_t v_subsingletonInstImplicitRhs_3783_ = stack[6].m_num;
lean_object* v_f_3784_ = stack[7].m_obj;
lean_object* v_info_3785_ = stack[8].m_obj;
lean_object* v_kinds_3786_ = stack[9].m_obj;
lean_object* v___y_3787_ = stack[10].m_obj;
lean_object* v___y_3788_ = stack[11].m_obj;
lean_object* v___y_3789_ = stack[12].m_obj;
lean_object* v___y_3790_ = stack[13].m_obj;
lean_object* v_res_3825_;
v_res_3825_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3777_, v_rhss_3778_, v_lhss_3779_, v_i_3780_, v_eqs_3781_, v_hyps_3782_, v_subsingletonInstImplicitRhs_3783_, v_f_3784_, v_info_3785_, v_kinds_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
stack->m_obj
 = v_res_3825_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed(lean_object* v_lhs_3826_, lean_object* v_rhss_3827_, lean_object* v_lhss_3828_, lean_object* v_i_3829_, lean_object* v_eqs_3830_, lean_object* v_hyps_3831_, lean_object* v_subsingletonInstImplicitRhs_3832_, lean_object* v_f_3833_, lean_object* v_info_3834_, lean_object* v_kinds_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_3841_; lean_object* v_res_3842_; 
v_subsingletonInstImplicitRhs_boxed_3841_ = lean_unbox(v_subsingletonInstImplicitRhs_3832_);
v_res_3842_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0(v_lhs_3826_, v_rhss_3827_, v_lhss_3828_, v_i_3829_, v_eqs_3830_, v_hyps_3831_, v_subsingletonInstImplicitRhs_boxed_3841_, v_f_3833_, v_info_3834_, v_kinds_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v_res_3842_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(uint8_t v_subsingletonInstImplicitRhs_3843_, lean_object* v_f_3844_, lean_object* v_info_3845_, lean_object* v_kinds_3846_, lean_object* v_lhss_3847_, lean_object* v_i_3848_, lean_object* v_rhss_3849_, lean_object* v_eqs_3850_, lean_object* v_hyps_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3864_ = lean_array_get_size(v_kinds_3846_);
v___x_3865_ = lean_nat_dec_eq(v_i_3848_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v_lhs_3868_; lean_object* v_hyps_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3866_ = l_Lean_instInhabitedExpr;
v___x_3867_ = 0;
v_lhs_3868_ = lean_array_get_borrowed(v___x_3866_, v_lhss_3847_, v_i_3848_);
lean_inc(v_lhs_3868_);
v_hyps_3869_ = lean_array_push(v_hyps_3851_, v_lhs_3868_);
v___x_3870_ = lean_box(v___x_3867_);
v___x_3871_ = lean_array_get(v___x_3870_, v_kinds_3846_, v_i_3848_);
lean_dec(v___x_3870_);
v___x_3872_ = lean_unbox(v___x_3871_);
lean_dec(v___x_3871_);
switch(v___x_3872_)
{
case 0:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_nat_add(v_i_3848_, v___x_3873_);
lean_dec(v_i_3848_);
lean_inc(v_lhs_3868_);
v___x_3875_ = lean_array_push(v_rhss_3849_, v_lhs_3868_);
v___x_3876_ = lean_box(0);
v___x_3877_ = lean_array_push(v_eqs_3850_, v___x_3876_);
v_i_3848_ = v___x_3874_;
v_rhss_3849_ = v___x_3875_;
v_eqs_3850_ = v___x_3877_;
v_hyps_3851_ = v_hyps_3869_;
goto _start;
}
case 2:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_inc(v_lhs_3868_);
v___x_3879_ = l_Lean_Expr_fvarId_x21(v_lhs_3868_);
v___x_3880_ = l_Lean_FVarId_getDecl___redArg(v___x_3879_, v_a_3852_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; lean_object* v___x_3886_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = l_Lean_LocalDecl_userName(v_a_3881_);
v___x_3883_ = l_Lean_LocalDecl_binderInfo(v_a_3881_);
v___x_3884_ = l_Lean_LocalDecl_type(v_a_3881_);
lean_dec(v_a_3881_);
v___x_3885_ = 0;
lean_inc(v___x_3882_);
v___x_3886_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_3848_, v_rhss_3849_, v_eqs_3850_, v_hyps_3869_, v_subsingletonInstImplicitRhs_3843_, v_f_3844_, v_info_3845_, v_kinds_3846_, v_lhss_3847_, v_lhs_3868_, v___x_3882_, v___x_3882_, v___x_3883_, v___x_3884_, v___x_3885_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
return v___x_3886_;
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_hyps_3869_);
lean_dec(v_lhs_3868_);
lean_dec_ref(v_eqs_3850_);
lean_dec_ref(v_rhss_3849_);
lean_dec(v_i_3848_);
lean_dec_ref(v_lhss_3847_);
lean_dec_ref(v_kinds_3846_);
lean_dec_ref(v_info_3845_);
lean_dec_ref(v_f_3844_);
v_a_3887_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3880_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3880_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
case 3:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = l_Lean_Meta_instInhabitedParamInfo_default;
lean_inc(v_a_3855_);
lean_inc_ref(v_a_3854_);
lean_inc(v_a_3853_);
lean_inc_ref(v_a_3852_);
lean_inc(v_lhs_3868_);
v___x_3896_ = lean_infer_type(v_lhs_3868_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v_paramInfo_3898_; lean_object* v___x_3899_; lean_object* v_backDeps_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v_paramInfo_3898_ = lean_ctor_get(v_info_3845_, 0);
v___x_3899_ = lean_array_get_borrowed(v___x_3895_, v_paramInfo_3898_, v_i_3848_);
v_backDeps_3900_ = lean_ctor_get(v___x_3899_, 0);
v___x_3901_ = lean_array_get_size(v_rhss_3849_);
v___x_3902_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lhss_3847_);
v___x_3903_ = l_Array_toSubarray___redArg(v_lhss_3847_, v___x_3902_, v___x_3901_);
v___x_3904_ = l_Subarray_copy___redArg(v___x_3903_);
v___x_3905_ = l_Lean_Expr_replaceFVars(v_a_3897_, v___x_3904_, v_rhss_3849_);
lean_dec_ref(v___x_3904_);
lean_dec(v_a_3897_);
v___x_3906_ = l_Lean_Expr_fvarId_x21(v_lhs_3868_);
v___x_3907_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast(v___x_3906_, v___x_3905_, v_backDeps_3900_, v_eqs_3850_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_add(v_i_3848_, v___x_3909_);
lean_dec(v_i_3848_);
v___x_3911_ = lean_array_push(v_rhss_3849_, v_a_3908_);
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_array_push(v_eqs_3850_, v___x_3912_);
v_i_3848_ = v___x_3910_;
v_rhss_3849_ = v___x_3911_;
v_eqs_3850_ = v___x_3913_;
v_hyps_3851_ = v_hyps_3869_;
goto _start;
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v_hyps_3869_);
lean_dec_ref(v_eqs_3850_);
lean_dec_ref(v_rhss_3849_);
lean_dec(v_i_3848_);
lean_dec_ref(v_lhss_3847_);
lean_dec_ref(v_kinds_3846_);
lean_dec_ref(v_info_3845_);
lean_dec_ref(v_f_3844_);
v_a_3915_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3907_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3907_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_hyps_3869_);
lean_dec_ref(v_eqs_3850_);
lean_dec_ref(v_rhss_3849_);
lean_dec(v_i_3848_);
lean_dec_ref(v_lhss_3847_);
lean_dec_ref(v_kinds_3846_);
lean_dec_ref(v_info_3845_);
lean_dec_ref(v_f_3844_);
v_a_3923_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3896_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3896_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
case 5:
{
lean_object* v___x_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_inc_n(v_lhs_3868_, 2);
v___x_3931_ = lean_box(v_subsingletonInstImplicitRhs_3843_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3932_, 0, v_lhs_3868_);
lean_closure_set(v___f_3932_, 1, v_rhss_3849_);
lean_closure_set(v___f_3932_, 2, v_lhss_3847_);
lean_closure_set(v___f_3932_, 3, v_i_3848_);
lean_closure_set(v___f_3932_, 4, v_eqs_3850_);
lean_closure_set(v___f_3932_, 5, v_hyps_3869_);
lean_closure_set(v___f_3932_, 6, v___x_3931_);
lean_closure_set(v___f_3932_, 7, v_f_3844_);
lean_closure_set(v___f_3932_, 8, v_info_3845_);
lean_closure_set(v___f_3932_, 9, v_kinds_3846_);
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_mk_empty_array_with_capacity(v___x_3933_);
v___x_3935_ = lean_array_push(v___x_3934_, v_lhs_3868_);
v___x_3936_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__1___redArg(v___x_3935_, v___f_3932_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
return v___x_3936_;
}
default: 
{
lean_dec_ref(v_hyps_3869_);
lean_dec_ref(v_eqs_3850_);
lean_dec_ref(v_rhss_3849_);
lean_dec(v_i_3848_);
lean_dec_ref(v_lhss_3847_);
lean_dec_ref(v_kinds_3846_);
lean_dec_ref(v_info_3845_);
lean_dec_ref(v_f_3844_);
v___y_3858_ = v_a_3852_;
v___y_3859_ = v_a_3853_;
v___y_3860_ = v_a_3854_;
v___y_3861_ = v_a_3855_;
goto v___jp_3857_;
}
}
}
else
{
lean_object* v_lhs_3937_; lean_object* v_rhs_3938_; lean_object* v___x_3939_; 
lean_dec_ref(v_eqs_3850_);
lean_dec(v_i_3848_);
lean_dec_ref(v_info_3845_);
lean_inc_ref(v_f_3844_);
v_lhs_3937_ = l_Lean_mkAppN(v_f_3844_, v_lhss_3847_);
lean_dec_ref(v_lhss_3847_);
v_rhs_3938_ = l_Lean_mkAppN(v_f_3844_, v_rhss_3849_);
lean_dec_ref(v_rhss_3849_);
v___x_3939_ = l_Lean_Meta_mkEq(v_lhs_3937_, v_rhs_3938_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; uint8_t v___x_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = 0;
v___x_3942_ = 1;
v___x_3943_ = l_Lean_Meta_mkForallFVars(v_hyps_3851_, v_a_3940_, v___x_3941_, v___x_3865_, v___x_3865_, v___x_3942_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec_ref(v_hyps_3851_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc_n(v_a_3944_, 2);
lean_dec_ref_known(v___x_3943_, 1);
lean_inc_ref(v_kinds_3846_);
v___x_3945_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof(v_a_3944_, v_kinds_3846_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3954_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3950_, 0, v_a_3944_);
lean_ctor_set(v___x_3950_, 1, v_a_3946_);
lean_ctor_set(v___x_3950_, 2, v_kinds_3846_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3950_);
v___x_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3944_);
lean_dec_ref(v_kinds_3846_);
v_a_3955_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3945_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3945_);
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
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_kinds_3846_);
v_a_3963_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3943_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3943_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v_hyps_3851_);
lean_dec_ref(v_kinds_3846_);
v_a_3971_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3939_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3939_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
v___jp_3857_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1_once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___closed__1);
v___x_3863_ = l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__0(v___x_3862_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_subsingletonInstImplicitRhs_3843_ = stack[0].m_num;
lean_object* v_f_3844_ = stack[1].m_obj;
lean_object* v_info_3845_ = stack[2].m_obj;
lean_object* v_kinds_3846_ = stack[3].m_obj;
lean_object* v_lhss_3847_ = stack[4].m_obj;
lean_object* v_i_3848_ = stack[5].m_obj;
lean_object* v_rhss_3849_ = stack[6].m_obj;
lean_object* v_eqs_3850_ = stack[7].m_obj;
lean_object* v_hyps_3851_ = stack[8].m_obj;
lean_object* v_a_3852_ = stack[9].m_obj;
lean_object* v_a_3853_ = stack[10].m_obj;
lean_object* v_a_3854_ = stack[11].m_obj;
lean_object* v_a_3855_ = stack[12].m_obj;
lean_object* v_res_3979_;
v_res_3979_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3843_, v_f_3844_, v_info_3845_, v_kinds_3846_, v_lhss_3847_, v_i_3848_, v_rhss_3849_, v_eqs_3850_, v_hyps_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
stack->m_obj
 = v_res_3979_;
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(lean_object* v_i_3980_, lean_object* v_rhss_3981_, lean_object* v_lhs_3982_, lean_object* v_eqs_3983_, lean_object* v_hyps_3984_, uint8_t v_subsingletonInstImplicitRhs_3985_, lean_object* v_f_3986_, lean_object* v_info_3987_, lean_object* v_kinds_3988_, lean_object* v_lhss_3989_, lean_object* v_b_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_3996_ = lean_unsigned_to_nat(1u);
v___x_3997_ = lean_nat_add(v_i_3980_, v___x_3996_);
lean_inc_ref(v_b_3990_);
v___x_3998_ = lean_array_push(v_rhss_3981_, v_b_3990_);
v___x_3999_ = l_Lean_Expr_fvarId_x21(v_lhs_3982_);
v___x_4000_ = l_Lean_Expr_fvarId_x21(v_b_3990_);
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_array_push(v_eqs_3983_, v___x_4002_);
v___x_4004_ = lean_array_push(v_hyps_3984_, v_b_3990_);
v___x_4005_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_3985_, v_f_3986_, v_info_3987_, v_kinds_3988_, v_lhss_3989_, v___x_3997_, v___x_3998_, v___x_4003_, v___x_4004_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v___x_4005_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3980_ = stack[0].m_obj;
lean_object* v_rhss_3981_ = stack[1].m_obj;
lean_object* v_lhs_3982_ = stack[2].m_obj;
lean_object* v_eqs_3983_ = stack[3].m_obj;
lean_object* v_hyps_3984_ = stack[4].m_obj;
uint8_t v_subsingletonInstImplicitRhs_3985_ = stack[5].m_num;
lean_object* v_f_3986_ = stack[6].m_obj;
lean_object* v_info_3987_ = stack[7].m_obj;
lean_object* v_kinds_3988_ = stack[8].m_obj;
lean_object* v_lhss_3989_ = stack[9].m_obj;
lean_object* v_b_3990_ = stack[10].m_obj;
lean_object* v___y_3991_ = stack[11].m_obj;
lean_object* v___y_3992_ = stack[12].m_obj;
lean_object* v___y_3993_ = stack[13].m_obj;
lean_object* v___y_3994_ = stack[14].m_obj;
lean_object* v_res_4006_;
v_res_4006_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_3980_, v_rhss_3981_, v_lhs_3982_, v_eqs_3983_, v_hyps_3984_, v_subsingletonInstImplicitRhs_3985_, v_f_3986_, v_info_3987_, v_kinds_3988_, v_lhss_3989_, v_b_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
stack->m_obj
 = v_res_4006_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed(lean_object* v_i_4007_, lean_object* v_rhss_4008_, lean_object* v_lhs_4009_, lean_object* v_eqs_4010_, lean_object* v_hyps_4011_, lean_object* v_subsingletonInstImplicitRhs_4012_, lean_object* v_f_4013_, lean_object* v_info_4014_, lean_object* v_kinds_4015_, lean_object* v_lhss_4016_, lean_object* v_b_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4023_; lean_object* v_res_4024_; 
v_subsingletonInstImplicitRhs_boxed_4023_ = lean_unbox(v_subsingletonInstImplicitRhs_4012_);
v_res_4024_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0(v_i_4007_, v_rhss_4008_, v_lhs_4009_, v_eqs_4010_, v_hyps_4011_, v_subsingletonInstImplicitRhs_boxed_4023_, v_f_4013_, v_info_4014_, v_kinds_4015_, v_lhss_4016_, v_b_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v_lhs_4009_);
lean_dec(v_i_4007_);
return v_res_4024_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(lean_object* v_i_4025_, lean_object* v_rhss_4026_, lean_object* v_lhs_4027_, lean_object* v_eqs_4028_, lean_object* v_hyps_4029_, uint8_t v_subsingletonInstImplicitRhs_4030_, lean_object* v_f_4031_, lean_object* v_info_4032_, lean_object* v_kinds_4033_, lean_object* v_lhss_4034_, lean_object* v_name_4035_, uint8_t v_bi_4036_, lean_object* v_type_4037_, uint8_t v_kind_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; lean_object* v___f_4045_; lean_object* v___x_4046_; 
v___x_4044_ = lean_box(v_subsingletonInstImplicitRhs_4030_);
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___lam__0___boxed), 16, 10);
lean_closure_set(v___f_4045_, 0, v_i_4025_);
lean_closure_set(v___f_4045_, 1, v_rhss_4026_);
lean_closure_set(v___f_4045_, 2, v_lhs_4027_);
lean_closure_set(v___f_4045_, 3, v_eqs_4028_);
lean_closure_set(v___f_4045_, 4, v_hyps_4029_);
lean_closure_set(v___f_4045_, 5, v___x_4044_);
lean_closure_set(v___f_4045_, 6, v_f_4031_);
lean_closure_set(v___f_4045_, 7, v_info_4032_);
lean_closure_set(v___f_4045_, 8, v_kinds_4033_);
lean_closure_set(v___f_4045_, 9, v_lhss_4034_);
v___x_4046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4035_, v_bi_4036_, v_type_4037_, v___f_4045_, v_kind_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_a_4055_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4046_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4046_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_4025_ = stack[0].m_obj;
lean_object* v_rhss_4026_ = stack[1].m_obj;
lean_object* v_lhs_4027_ = stack[2].m_obj;
lean_object* v_eqs_4028_ = stack[3].m_obj;
lean_object* v_hyps_4029_ = stack[4].m_obj;
uint8_t v_subsingletonInstImplicitRhs_4030_ = stack[5].m_num;
lean_object* v_f_4031_ = stack[6].m_obj;
lean_object* v_info_4032_ = stack[7].m_obj;
lean_object* v_kinds_4033_ = stack[8].m_obj;
lean_object* v_lhss_4034_ = stack[9].m_obj;
lean_object* v_name_4035_ = stack[10].m_obj;
uint8_t v_bi_4036_ = stack[11].m_num;
lean_object* v_type_4037_ = stack[12].m_obj;
uint8_t v_kind_4038_ = stack[13].m_num;
lean_object* v___y_4039_ = stack[14].m_obj;
lean_object* v___y_4040_ = stack[15].m_obj;
lean_object* v___y_4041_ = stack[16].m_obj;
lean_object* v___y_4042_ = stack[17].m_obj;
lean_object* v_res_4063_;
v_res_4063_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_4025_, v_rhss_4026_, v_lhs_4027_, v_eqs_4028_, v_hyps_4029_, v_subsingletonInstImplicitRhs_4030_, v_f_4031_, v_info_4032_, v_kinds_4033_, v_lhss_4034_, v_name_4035_, v_bi_4036_, v_type_4037_, v_kind_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
stack->m_obj
 = v_res_4063_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4___boxed(lean_object** _args){
lean_object* v_i_4064_ = _args[0];
lean_object* v_rhss_4065_ = _args[1];
lean_object* v_lhs_4066_ = _args[2];
lean_object* v_eqs_4067_ = _args[3];
lean_object* v_hyps_4068_ = _args[4];
lean_object* v_subsingletonInstImplicitRhs_4069_ = _args[5];
lean_object* v_f_4070_ = _args[6];
lean_object* v_info_4071_ = _args[7];
lean_object* v_kinds_4072_ = _args[8];
lean_object* v_lhss_4073_ = _args[9];
lean_object* v_name_4074_ = _args[10];
lean_object* v_bi_4075_ = _args[11];
lean_object* v_type_4076_ = _args[12];
lean_object* v_kind_4077_ = _args[13];
lean_object* v___y_4078_ = _args[14];
lean_object* v___y_4079_ = _args[15];
lean_object* v___y_4080_ = _args[16];
lean_object* v___y_4081_ = _args[17];
lean_object* v___y_4082_ = _args[18];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4083_; uint8_t v_bi_boxed_4084_; uint8_t v_kind_boxed_4085_; lean_object* v_res_4086_; 
v_subsingletonInstImplicitRhs_boxed_4083_ = lean_unbox(v_subsingletonInstImplicitRhs_4069_);
v_bi_boxed_4084_ = lean_unbox(v_bi_4075_);
v_kind_boxed_4085_ = lean_unbox(v_kind_4077_);
v_res_4086_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__4(v_i_4064_, v_rhss_4065_, v_lhs_4066_, v_eqs_4067_, v_hyps_4068_, v_subsingletonInstImplicitRhs_boxed_4083_, v_f_4070_, v_info_4071_, v_kinds_4072_, v_lhss_4073_, v_name_4074_, v_bi_boxed_4084_, v_type_4076_, v_kind_boxed_4085_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5___boxed(lean_object** _args){
lean_object* v_i_4087_ = _args[0];
lean_object* v_rhss_4088_ = _args[1];
lean_object* v_eqs_4089_ = _args[2];
lean_object* v_hyps_4090_ = _args[3];
lean_object* v_subsingletonInstImplicitRhs_4091_ = _args[4];
lean_object* v_f_4092_ = _args[5];
lean_object* v_info_4093_ = _args[6];
lean_object* v_kinds_4094_ = _args[7];
lean_object* v_lhss_4095_ = _args[8];
lean_object* v_lhs_4096_ = _args[9];
lean_object* v___x_4097_ = _args[10];
lean_object* v_name_4098_ = _args[11];
lean_object* v_bi_4099_ = _args[12];
lean_object* v_type_4100_ = _args[13];
lean_object* v_kind_4101_ = _args[14];
lean_object* v___y_4102_ = _args[15];
lean_object* v___y_4103_ = _args[16];
lean_object* v___y_4104_ = _args[17];
lean_object* v___y_4105_ = _args[18];
lean_object* v___y_4106_ = _args[19];
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4107_; uint8_t v_bi_boxed_4108_; uint8_t v_kind_boxed_4109_; lean_object* v_res_4110_; 
v_subsingletonInstImplicitRhs_boxed_4107_ = lean_unbox(v_subsingletonInstImplicitRhs_4091_);
v_bi_boxed_4108_ = lean_unbox(v_bi_4099_);
v_kind_boxed_4109_ = lean_unbox(v_kind_4101_);
v_res_4110_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs_loop_spec__0_spec__0___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go_spec__5(v_i_4087_, v_rhss_4088_, v_eqs_4089_, v_hyps_4090_, v_subsingletonInstImplicitRhs_boxed_4107_, v_f_4092_, v_info_4093_, v_kinds_4094_, v_lhss_4095_, v_lhs_4096_, v___x_4097_, v_name_4098_, v_bi_boxed_4108_, v_type_4100_, v_kind_boxed_4109_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go___boxed(lean_object* v_subsingletonInstImplicitRhs_4111_, lean_object* v_f_4112_, lean_object* v_info_4113_, lean_object* v_kinds_4114_, lean_object* v_lhss_4115_, lean_object* v_i_4116_, lean_object* v_rhss_4117_, lean_object* v_eqs_4118_, lean_object* v_hyps_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4125_; lean_object* v_res_4126_; 
v_subsingletonInstImplicitRhs_boxed_4125_ = lean_unbox(v_subsingletonInstImplicitRhs_4111_);
v_res_4126_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_boxed_4125_, v_f_4112_, v_info_4113_, v_kinds_4114_, v_lhss_4115_, v_i_4116_, v_rhss_4117_, v_eqs_4118_, v_hyps_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
return v_res_4126_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(lean_object* v___x_4127_, uint8_t v_subsingletonInstImplicitRhs_4128_, lean_object* v_f_4129_, lean_object* v_info_4130_, lean_object* v_kinds_4131_, lean_object* v_lhss_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = lean_array_get_size(v_lhss_4132_);
v___x_4140_ = lean_nat_dec_eq(v___x_4139_, v___x_4127_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec_ref(v_lhss_4132_);
lean_dec_ref(v_kinds_4131_);
lean_dec_ref(v_info_4130_);
lean_dec_ref(v_f_4129_);
v___x_4141_ = lean_box(0);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
else
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4143_ = lean_unsigned_to_nat(0u);
v___x_4144_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_withNewEqs___redArg___closed__0));
v___x_4145_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_go(v_subsingletonInstImplicitRhs_4128_, v_f_4129_, v_info_4130_, v_kinds_4131_, v_lhss_4132_, v___x_4143_, v___x_4144_, v___x_4144_, v___x_4144_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_a_4146_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4150_);
v___x_4152_ = v___x_4148_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4145_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4145_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4127_ = stack[0].m_obj;
uint8_t v_subsingletonInstImplicitRhs_4128_ = stack[1].m_num;
lean_object* v_f_4129_ = stack[2].m_obj;
lean_object* v_info_4130_ = stack[3].m_obj;
lean_object* v_kinds_4131_ = stack[4].m_obj;
lean_object* v_lhss_4132_ = stack[5].m_obj;
lean_object* v_x_4133_ = stack[6].m_obj;
lean_object* v___y_4134_ = stack[7].m_obj;
lean_object* v___y_4135_ = stack[8].m_obj;
lean_object* v___y_4136_ = stack[9].m_obj;
lean_object* v___y_4137_ = stack[10].m_obj;
lean_object* v_res_4163_;
v_res_4163_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4127_, v_subsingletonInstImplicitRhs_4128_, v_f_4129_, v_info_4130_, v_kinds_4131_, v_lhss_4132_, v_x_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
stack->m_obj
 = v_res_4163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed(lean_object* v___x_4164_, lean_object* v_subsingletonInstImplicitRhs_4165_, lean_object* v_f_4166_, lean_object* v_info_4167_, lean_object* v_kinds_4168_, lean_object* v_lhss_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4176_; lean_object* v_res_4177_; 
v_subsingletonInstImplicitRhs_boxed_4176_ = lean_unbox(v_subsingletonInstImplicitRhs_4165_);
v_res_4177_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0(v___x_4164_, v_subsingletonInstImplicitRhs_boxed_4176_, v_f_4166_, v_info_4167_, v_kinds_4168_, v_lhss_4169_, v_x_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec_ref(v_x_4170_);
lean_dec(v___x_4164_);
return v_res_4177_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(uint8_t v_subsingletonInstImplicitRhs_4178_, lean_object* v_f_4179_, lean_object* v_info_4180_, lean_object* v_kinds_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v_a_4194_; lean_object* v___x_4197_; 
lean_inc(v_a_4185_);
lean_inc_ref(v_a_4184_);
lean_inc(v_a_4183_);
lean_inc_ref(v_a_4182_);
lean_inc_ref(v_f_4179_);
v___x_4197_ = lean_infer_type(v_f_4179_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4212_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4212_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4212_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___x_4206_; 
v___x_4202_ = lean_array_get_size(v_kinds_4181_);
v___x_4203_ = lean_box(v_subsingletonInstImplicitRhs_4178_);
v___f_4204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4204_, 0, v___x_4202_);
lean_closure_set(v___f_4204_, 1, v___x_4203_);
lean_closure_set(v___f_4204_, 2, v_f_4179_);
lean_closure_set(v___f_4204_, 3, v_info_4180_);
lean_closure_set(v___f_4204_, 4, v_kinds_4181_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 1);
lean_ctor_set(v___x_4200_, 0, v___x_4202_);
v___x_4206_ = v___x_4200_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4202_);
v___x_4206_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
uint8_t v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = 1;
v___x_4208_ = 0;
v___x_4209_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkHCongrWithArity_mkProof_spec__0___redArg(v_a_4198_, v___x_4206_, v___f_4204_, v___x_4207_, v___x_4208_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4209_) == 0)
{
return v___x_4209_;
}
else
{
lean_object* v_a_4210_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v_a_4194_ = v_a_4210_;
goto v___jp_4193_;
}
}
}
}
else
{
lean_object* v_a_4213_; 
lean_dec_ref(v_kinds_4181_);
lean_dec_ref(v_info_4180_);
lean_dec_ref(v_f_4179_);
v_a_4213_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4197_, 1);
v_a_4194_ = v_a_4213_;
goto v___jp_4193_;
}
v___jp_4187_:
{
if (v___y_4189_ == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
lean_dec_ref(v___y_4188_);
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
else
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___y_4188_);
return v___x_4192_;
}
}
v___jp_4193_:
{
uint8_t v___x_4195_; 
v___x_4195_ = l_Lean_Exception_isInterrupt(v_a_4194_);
if (v___x_4195_ == 0)
{
uint8_t v___x_4196_; 
lean_inc_ref(v_a_4194_);
v___x_4196_ = l_Lean_Exception_isRuntime(v_a_4194_);
v___y_4188_ = v_a_4194_;
v___y_4189_ = v___x_4196_;
goto v___jp_4187_;
}
else
{
v___y_4188_ = v_a_4194_;
v___y_4189_ = v___x_4195_;
goto v___jp_4187_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f_0interp(lean_interpreter_value* stack)
{
uint8_t v_subsingletonInstImplicitRhs_4178_ = stack[0].m_num;
lean_object* v_f_4179_ = stack[1].m_obj;
lean_object* v_info_4180_ = stack[2].m_obj;
lean_object* v_kinds_4181_ = stack[3].m_obj;
lean_object* v_a_4182_ = stack[4].m_obj;
lean_object* v_a_4183_ = stack[5].m_obj;
lean_object* v_a_4184_ = stack[6].m_obj;
lean_object* v_a_4185_ = stack[7].m_obj;
lean_object* v_res_4214_;
v_res_4214_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4178_, v_f_4179_, v_info_4180_, v_kinds_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
stack->m_obj
 = v_res_4214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f___boxed(lean_object* v_subsingletonInstImplicitRhs_4215_, lean_object* v_f_4216_, lean_object* v_info_4217_, lean_object* v_kinds_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4224_; lean_object* v_res_4225_; 
v_subsingletonInstImplicitRhs_boxed_4224_ = lean_unbox(v_subsingletonInstImplicitRhs_4215_);
v_res_4225_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_boxed_4224_, v_f_4216_, v_info_4217_, v_kinds_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
return v_res_4225_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(size_t v_sz_4226_, size_t v_i_4227_, lean_object* v_bs_4228_){
_start:
{
uint8_t v___x_4229_; 
v___x_4229_ = lean_usize_dec_lt(v_i_4227_, v_sz_4226_);
if (v___x_4229_ == 0)
{
return v_bs_4228_;
}
else
{
lean_object* v_v_4230_; lean_object* v___x_4231_; lean_object* v_bs_x27_4232_; uint8_t v___y_4234_; uint8_t v___x_4240_; 
v_v_4230_ = lean_array_uget(v_bs_4228_, v_i_4227_);
v___x_4231_ = lean_unsigned_to_nat(0u);
v_bs_x27_4232_ = lean_array_uset(v_bs_4228_, v_i_4227_, v___x_4231_);
v___x_4240_ = lean_unbox(v_v_4230_);
switch(v___x_4240_)
{
case 3:
{
uint8_t v___x_4241_; 
lean_dec(v_v_4230_);
v___x_4241_ = 0;
v___y_4234_ = v___x_4241_;
goto v___jp_4233_;
}
case 5:
{
uint8_t v___x_4242_; 
lean_dec(v_v_4230_);
v___x_4242_ = 0;
v___y_4234_ = v___x_4242_;
goto v___jp_4233_;
}
default: 
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_unbox(v_v_4230_);
lean_dec(v_v_4230_);
v___y_4234_ = v___x_4243_;
goto v___jp_4233_;
}
}
v___jp_4233_:
{
size_t v___x_4235_; size_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4235_ = ((size_t)1ULL);
v___x_4236_ = lean_usize_add(v_i_4227_, v___x_4235_);
v___x_4237_ = lean_box(v___y_4234_);
v___x_4238_ = lean_array_uset(v_bs_x27_4232_, v_i_4227_, v___x_4237_);
v_i_4227_ = v___x_4236_;
v_bs_4228_ = v___x_4238_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4226_ = stack[0].m_num;
size_t v_i_4227_ = stack[1].m_num;
lean_object* v_bs_4228_ = stack[2].m_obj;
lean_object* v_res_4244_;
v_res_4244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4226_, v_i_4227_, v_bs_4228_);
stack->m_obj
 = v_res_4244_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0___boxed(lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_bs_4247_){
_start:
{
size_t v_sz_boxed_4248_; size_t v_i_boxed_4249_; lean_object* v_res_4250_; 
v_sz_boxed_4248_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4249_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_boxed_4248_, v_i_boxed_4249_, v_bs_4247_);
return v_res_4250_;
}
}
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object* v_f_4251_, lean_object* v_info_4252_, lean_object* v_kinds_4253_, uint8_t v_subsingletonInstImplicitRhs_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v___x_4260_; 
lean_inc_ref(v_kinds_4253_);
lean_inc_ref(v_info_4252_);
lean_inc_ref(v_f_4251_);
v___x_4260_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4254_, v_f_4251_, v_info_4252_, v_kinds_4253_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
if (lean_obj_tag(v_a_4261_) == 1)
{
lean_dec_ref(v_kinds_4253_);
lean_dec_ref(v_info_4252_);
lean_dec_ref(v_f_4251_);
return v___x_4260_;
}
else
{
lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4274_; 
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; 
v_unused_4275_ = lean_ctor_get(v___x_4260_, 0);
lean_dec(v_unused_4275_);
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4274_;
goto v_resetjp_4262_;
}
else
{
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4274_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
uint8_t v___x_4265_; 
v___x_4265_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_hasCastLike(v_kinds_4253_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4268_; 
lean_dec_ref(v_kinds_4253_);
lean_dec_ref(v_info_4252_);
lean_dec_ref(v_f_4251_);
v___x_4266_ = lean_box(0);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4266_);
v___x_4268_ = v___x_4263_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
else
{
size_t v_sz_4270_; size_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_del_object(v___x_4263_);
v_sz_4270_ = lean_array_size(v_kinds_4253_);
v___x_4271_ = ((size_t)0ULL);
v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkCongrSimpCore_x3f_spec__0(v_sz_4270_, v___x_4271_, v_kinds_4253_);
v___x_4273_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mk_x3f(v_subsingletonInstImplicitRhs_4254_, v_f_4251_, v_info_4252_, v___x_4272_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
return v___x_4273_;
}
}
}
}
else
{
lean_dec_ref(v_kinds_4253_);
lean_dec_ref(v_info_4252_);
lean_dec_ref(v_f_4251_);
return v___x_4260_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkCongrSimpCore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4251_ = stack[0].m_obj;
lean_object* v_info_4252_ = stack[1].m_obj;
lean_object* v_kinds_4253_ = stack[2].m_obj;
uint8_t v_subsingletonInstImplicitRhs_4254_ = stack[3].m_num;
lean_object* v_a_4255_ = stack[4].m_obj;
lean_object* v_a_4256_ = stack[5].m_obj;
lean_object* v_a_4257_ = stack[6].m_obj;
lean_object* v_a_4258_ = stack[7].m_obj;
lean_object* v_res_4276_;
v_res_4276_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4251_, v_info_4252_, v_kinds_4253_, v_subsingletonInstImplicitRhs_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
stack->m_obj
 = v_res_4276_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpCore_x3f___boxed(lean_object* v_f_4277_, lean_object* v_info_4278_, lean_object* v_kinds_4279_, lean_object* v_subsingletonInstImplicitRhs_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4286_; lean_object* v_res_4287_; 
v_subsingletonInstImplicitRhs_boxed_4286_ = lean_unbox(v_subsingletonInstImplicitRhs_4280_);
v_res_4287_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_4277_, v_info_4278_, v_kinds_4279_, v_subsingletonInstImplicitRhs_boxed_4286_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
return v_res_4287_;
}
}
lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object* v_f_4288_, uint8_t v_subsingletonInstImplicitRhs_4289_, lean_object* v_maxArgs_x3f_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___x_4296_; lean_object* v_a_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4296_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_spec__4___redArg(v_f_4288_, v_a_4292_);
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
v___x_4298_ = l_Lean_Expr_cleanupAnnotations(v_a_4297_);
lean_inc_ref(v___x_4298_);
v___x_4299_ = l_Lean_Meta_getFunInfo(v___x_4298_, v_maxArgs_x3f_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
lean_inc_ref(v___x_4298_);
v___x_4301_ = l_Lean_Meta_getCongrSimpKinds(v___x_4298_, v_a_4300_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4298_, v_a_4300_, v_a_4302_, v_subsingletonInstImplicitRhs_4289_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
return v___x_4303_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v_a_4300_);
lean_dec_ref(v___x_4298_);
v_a_4304_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4301_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4301_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec_ref(v___x_4298_);
v_a_4312_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4299_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4299_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkCongrSimp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4288_ = stack[0].m_obj;
uint8_t v_subsingletonInstImplicitRhs_4289_ = stack[1].m_num;
lean_object* v_maxArgs_x3f_4290_ = stack[2].m_obj;
lean_object* v_a_4291_ = stack[3].m_obj;
lean_object* v_a_4292_ = stack[4].m_obj;
lean_object* v_a_4293_ = stack[5].m_obj;
lean_object* v_a_4294_ = stack[6].m_obj;
lean_object* v_res_4320_;
v_res_4320_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4288_, v_subsingletonInstImplicitRhs_4289_, v_maxArgs_x3f_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
stack->m_obj
 = v_res_4320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimp_x3f___boxed(lean_object* v_f_4321_, lean_object* v_subsingletonInstImplicitRhs_4322_, lean_object* v_maxArgs_x3f_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
uint8_t v_subsingletonInstImplicitRhs_boxed_4329_; lean_object* v_res_4330_; 
v_subsingletonInstImplicitRhs_boxed_4329_ = lean_unbox(v_subsingletonInstImplicitRhs_4322_);
v_res_4330_ = l_Lean_Meta_mkCongrSimp_x3f(v_f_4321_, v_subsingletonInstImplicitRhs_boxed_4329_, v_maxArgs_x3f_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
return v_res_4330_;
}
}
uint8_t l_Lean_Meta_isHCongrReservedNameSuffix(lean_object* v_s_4335_){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4336_ = lean_string_utf8_byte_size(v_s_4335_);
v___x_4337_ = lean_unsigned_to_nat(7u);
v___x_4338_ = lean_nat_dec_le(v___x_4337_, v___x_4336_);
if (v___x_4338_ == 0)
{
lean_dec_ref(v_s_4335_);
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4339_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_string_memcmp(v_s_4335_, v___x_4339_, v___x_4340_, v___x_4340_, v___x_4337_);
if (v___x_4341_ == 0)
{
lean_dec_ref(v_s_4335_);
return v___x_4341_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
lean_inc_ref(v_s_4335_);
v___x_4342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4342_, 0, v_s_4335_);
lean_ctor_set(v___x_4342_, 1, v___x_4340_);
lean_ctor_set(v___x_4342_, 2, v___x_4336_);
v___x_4343_ = l_String_Slice_Pos_nextn(v___x_4342_, v___x_4340_, v___x_4337_);
lean_dec_ref_known(v___x_4342_, 3);
v___x_4344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4344_, 0, v_s_4335_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
lean_ctor_set(v___x_4344_, 2, v___x_4336_);
v___x_4345_ = l_String_Slice_isNat(v___x_4344_);
lean_dec_ref_known(v___x_4344_, 3);
return v___x_4345_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isHCongrReservedNameSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4335_ = stack[0].m_obj;
uint8_t v_res_4346_;
v_res_4346_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4335_);
stack->m_num = v_res_4346_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isHCongrReservedNameSuffix___boxed(lean_object* v_s_4347_){
_start:
{
uint8_t v_res_4348_; lean_object* v_r_4349_; 
v_res_4348_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_s_4347_);
v_r_4349_ = lean_box(v_res_4348_);
return v_r_4349_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = lean_unsigned_to_nat(3482611248u);
v___x_4400_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4401_ = l_Lean_Name_num___override(v___x_4400_, v___x_4399_);
return v___x_4401_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4403_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4404_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4405_ = l_Lean_Name_str___override(v___x_4404_, v___x_4403_);
return v___x_4405_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4407_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4408_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4409_ = l_Lean_Name_str___override(v___x_4408_, v___x_4407_);
return v___x_4409_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = lean_unsigned_to_nat(2u);
v___x_4411_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4412_ = l_Lean_Name_num___override(v___x_4411_, v___x_4410_);
return v___x_4412_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4414_; uint8_t v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4415_ = 0;
v___x_4416_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_);
v___x_4417_ = l_Lean_registerTraceClass(v___x_4414_, v___x_4415_, v___x_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4418_;
v_res_4418_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4418_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2____boxed(lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
return v_res_4420_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(lean_object* v_env_4421_, lean_object* v_as_4422_, size_t v_i_4423_, size_t v_stop_4424_, lean_object* v_b_4425_){
_start:
{
lean_object* v___y_4427_; uint8_t v___x_4431_; 
v___x_4431_ = lean_usize_dec_eq(v_i_4423_, v_stop_4424_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v_fst_4433_; uint8_t v___x_4434_; 
v___x_4432_ = lean_array_uget_borrowed(v_as_4422_, v_i_4423_);
v_fst_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_fst_4433_);
lean_inc_ref(v_env_4421_);
v___x_4434_ = l_Lean_Environment_contains(v_env_4421_, v_fst_4433_, v___x_4431_);
if (v___x_4434_ == 0)
{
v___y_4427_ = v_b_4425_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4435_; 
lean_inc(v___x_4432_);
v___x_4435_ = lean_array_push(v_b_4425_, v___x_4432_);
v___y_4427_ = v___x_4435_;
goto v___jp_4426_;
}
}
else
{
lean_dec_ref(v_env_4421_);
return v_b_4425_;
}
v___jp_4426_:
{
size_t v___x_4428_; size_t v___x_4429_; 
v___x_4428_ = ((size_t)1ULL);
v___x_4429_ = lean_usize_add(v_i_4423_, v___x_4428_);
v_i_4423_ = v___x_4429_;
v_b_4425_ = v___y_4427_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4421_ = stack[0].m_obj;
lean_object* v_as_4422_ = stack[1].m_obj;
size_t v_i_4423_ = stack[2].m_num;
size_t v_stop_4424_ = stack[3].m_num;
lean_object* v_b_4425_ = stack[4].m_obj;
lean_object* v_res_4436_;
v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4421_, v_as_4422_, v_i_4423_, v_stop_4424_, v_b_4425_);
stack->m_obj
 = v_res_4436_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_4437_, lean_object* v_as_4438_, lean_object* v_i_4439_, lean_object* v_stop_4440_, lean_object* v_b_4441_){
_start:
{
size_t v_i_boxed_4442_; size_t v_stop_boxed_4443_; lean_object* v_res_4444_; 
v_i_boxed_4442_ = lean_unbox_usize(v_i_4439_);
lean_dec(v_i_4439_);
v_stop_boxed_4443_ = lean_unbox_usize(v_stop_4440_);
lean_dec(v_stop_4440_);
v_res_4444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4437_, v_as_4438_, v_i_boxed_4442_, v_stop_boxed_4443_, v_b_4441_);
lean_dec_ref(v_as_4438_);
return v_res_4444_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(lean_object* v_env_4445_, lean_object* v_as_4446_, size_t v_i_4447_, size_t v_stop_4448_, lean_object* v_b_4449_){
_start:
{
lean_object* v___y_4451_; uint8_t v___x_4455_; 
v___x_4455_ = lean_usize_dec_eq(v_i_4447_, v_stop_4448_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v_fst_4457_; uint8_t v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4456_ = lean_array_uget_borrowed(v_as_4446_, v_i_4447_);
v_fst_4457_ = lean_ctor_get(v___x_4456_, 0);
v___x_4458_ = 1;
lean_inc_ref(v_env_4445_);
v___x_4459_ = l_Lean_Environment_setExporting(v_env_4445_, v___x_4458_);
lean_inc(v_fst_4457_);
v___x_4460_ = l_Lean_Environment_contains(v___x_4459_, v_fst_4457_, v___x_4458_);
if (v___x_4460_ == 0)
{
v___y_4451_ = v_b_4449_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4461_; 
lean_inc(v___x_4456_);
v___x_4461_ = lean_array_push(v_b_4449_, v___x_4456_);
v___y_4451_ = v___x_4461_;
goto v___jp_4450_;
}
}
else
{
lean_dec_ref(v_env_4445_);
return v_b_4449_;
}
v___jp_4450_:
{
size_t v___x_4452_; size_t v___x_4453_; 
v___x_4452_ = ((size_t)1ULL);
v___x_4453_ = lean_usize_add(v_i_4447_, v___x_4452_);
v_i_4447_ = v___x_4453_;
v_b_4449_ = v___y_4451_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4445_ = stack[0].m_obj;
lean_object* v_as_4446_ = stack[1].m_obj;
size_t v_i_4447_ = stack[2].m_num;
size_t v_stop_4448_ = stack[3].m_num;
lean_object* v_b_4449_ = stack[4].m_obj;
lean_object* v_res_4462_;
v_res_4462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4445_, v_as_4446_, v_i_4447_, v_stop_4448_, v_b_4449_);
stack->m_obj
 = v_res_4462_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_4463_, lean_object* v_as_4464_, lean_object* v_i_4465_, lean_object* v_stop_4466_, lean_object* v_b_4467_){
_start:
{
size_t v_i_boxed_4468_; size_t v_stop_boxed_4469_; lean_object* v_res_4470_; 
v_i_boxed_4468_ = lean_unbox_usize(v_i_4465_);
lean_dec(v_i_4465_);
v_stop_boxed_4469_ = lean_unbox_usize(v_stop_4466_);
lean_dec(v_stop_4466_);
v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4463_, v_as_4464_, v_i_boxed_4468_, v_stop_boxed_4469_, v_b_4467_);
lean_dec_ref(v_as_4464_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_4471_, lean_object* v_x_4472_){
_start:
{
if (lean_obj_tag(v_x_4472_) == 0)
{
lean_object* v_k_4473_; lean_object* v_v_4474_; lean_object* v_l_4475_; lean_object* v_r_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_k_4473_ = lean_ctor_get(v_x_4472_, 1);
v_v_4474_ = lean_ctor_get(v_x_4472_, 2);
v_l_4475_ = lean_ctor_get(v_x_4472_, 3);
v_r_4476_ = lean_ctor_get(v_x_4472_, 4);
v___x_4477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4471_, v_l_4475_);
lean_inc(v_v_4474_);
lean_inc(v_k_4473_);
v___x_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4478_, 0, v_k_4473_);
lean_ctor_set(v___x_4478_, 1, v_v_4474_);
v___x_4479_ = lean_array_push(v___x_4477_, v___x_4478_);
v_init_4471_ = v___x_4479_;
v_x_4472_ = v_r_4476_;
goto _start;
}
else
{
return v_init_4471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_4481_, lean_object* v_x_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4481_, v_x_4482_);
lean_dec(v_x_4482_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(lean_object* v_env_4488_, lean_object* v_s_4489_){
_start:
{
lean_object* v___x_4490_; lean_object* v___y_4492_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4490_ = lean_unsigned_to_nat(0u);
v___x_4507_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4508_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v___x_4507_, v_s_4489_);
v___x_4509_ = lean_array_get_size(v___x_4508_);
v___x_4510_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4511_ = lean_nat_dec_lt(v___x_4490_, v___x_4509_);
if (v___x_4511_ == 0)
{
lean_dec_ref(v___x_4508_);
v___y_4492_ = v___x_4510_;
goto v___jp_4491_;
}
else
{
uint8_t v___x_4512_; 
v___x_4512_ = lean_nat_dec_le(v___x_4509_, v___x_4509_);
if (v___x_4512_ == 0)
{
if (v___x_4511_ == 0)
{
lean_dec_ref(v___x_4508_);
v___y_4492_ = v___x_4510_;
goto v___jp_4491_;
}
else
{
size_t v___x_4513_; size_t v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = ((size_t)0ULL);
v___x_4514_ = lean_usize_of_nat(v___x_4509_);
lean_inc_ref(v_env_4488_);
v___x_4515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4488_, v___x_4508_, v___x_4513_, v___x_4514_, v___x_4510_);
lean_dec_ref(v___x_4508_);
v___y_4492_ = v___x_4515_;
goto v___jp_4491_;
}
}
else
{
size_t v___x_4516_; size_t v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = ((size_t)0ULL);
v___x_4517_ = lean_usize_of_nat(v___x_4509_);
lean_inc_ref(v_env_4488_);
v___x_4518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__2(v_env_4488_, v___x_4508_, v___x_4516_, v___x_4517_, v___x_4510_);
lean_dec_ref(v___x_4508_);
v___y_4492_ = v___x_4518_;
goto v___jp_4491_;
}
}
v___jp_4491_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4493_ = lean_array_get_size(v___y_4492_);
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4495_ = lean_nat_dec_lt(v___x_4490_, v___x_4493_);
if (v___x_4495_ == 0)
{
lean_object* v___x_4496_; 
lean_dec_ref(v_env_4488_);
v___x_4496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4494_);
lean_ctor_set(v___x_4496_, 1, v___x_4494_);
lean_ctor_set(v___x_4496_, 2, v___y_4492_);
return v___x_4496_;
}
else
{
uint8_t v___x_4497_; 
v___x_4497_ = lean_nat_dec_le(v___x_4493_, v___x_4493_);
if (v___x_4497_ == 0)
{
if (v___x_4495_ == 0)
{
lean_object* v___x_4498_; 
lean_dec_ref(v_env_4488_);
v___x_4498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4494_);
lean_ctor_set(v___x_4498_, 1, v___x_4494_);
lean_ctor_set(v___x_4498_, 2, v___y_4492_);
return v___x_4498_;
}
else
{
size_t v___x_4499_; size_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4499_ = ((size_t)0ULL);
v___x_4500_ = lean_usize_of_nat(v___x_4493_);
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4488_, v___y_4492_, v___x_4499_, v___x_4500_, v___x_4494_);
lean_inc_ref(v___x_4501_);
v___x_4502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
lean_ctor_set(v___x_4502_, 2, v___y_4492_);
return v___x_4502_;
}
}
else
{
size_t v___x_4503_; size_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4503_ = ((size_t)0ULL);
v___x_4504_ = lean_usize_of_nat(v___x_4493_);
v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__1(v_env_4488_, v___y_4492_, v___x_4503_, v___x_4504_, v___x_4494_);
lean_inc_ref(v___x_4505_);
v___x_4506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
lean_ctor_set(v___x_4506_, 2, v___y_4492_);
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_env_4519_, lean_object* v_s_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(v_env_4519_, v_s_4520_);
lean_dec(v_s_4520_);
return v_res_4521_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; 
v___f_4531_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4532_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_));
v___x_4534_ = 0;
v___x_4535_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_4532_, v___x_4533_, v___x_4534_, v___f_4531_);
return v___x_4535_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4536_;
v_res_4536_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4536_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2____boxed(lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(lean_object* v_init_4539_, lean_object* v_t_4540_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0_spec__0(v_init_4539_, v_t_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4542_, lean_object* v_t_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2__spec__0(v_init_4542_, v_t_4543_);
lean_dec(v_t_4543_);
return v_res_4544_;
}
}
uint8_t l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(lean_object* v_env_4545_, lean_object* v_n_4546_){
_start:
{
if (lean_obj_tag(v_n_4546_) == 1)
{
lean_object* v_pre_4547_; lean_object* v_str_4548_; uint8_t v___y_4550_; uint8_t v___x_4552_; 
v_pre_4547_ = lean_ctor_get(v_n_4546_, 0);
lean_inc(v_pre_4547_);
v_str_4548_ = lean_ctor_get(v_n_4546_, 1);
lean_inc_ref_n(v_str_4548_, 2);
lean_dec_ref_known(v_n_4546_, 2);
v___x_4552_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4548_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; uint8_t v___x_4554_; 
v___x_4553_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4554_ = lean_string_dec_eq(v_str_4548_, v___x_4553_);
lean_dec_ref(v_str_4548_);
v___y_4550_ = v___x_4554_;
goto v___jp_4549_;
}
else
{
lean_dec_ref(v_str_4548_);
v___y_4550_ = v___x_4552_;
goto v___jp_4549_;
}
v___jp_4549_:
{
if (v___y_4550_ == 0)
{
lean_dec(v_pre_4547_);
lean_dec_ref(v_env_4545_);
return v___y_4550_;
}
else
{
uint8_t v___x_4551_; 
v___x_4551_ = l_Lean_Environment_contains(v_env_4545_, v_pre_4547_, v___y_4550_);
return v___x_4551_;
}
}
}
else
{
uint8_t v___x_4555_; 
lean_dec(v_n_4546_);
lean_dec_ref(v_env_4545_);
v___x_4555_ = 0;
return v___x_4555_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4545_ = stack[0].m_obj;
lean_object* v_n_4546_ = stack[1].m_obj;
uint8_t v_res_4556_;
v_res_4556_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4545_, v_n_4546_);
stack->m_num = v_res_4556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_env_4557_, lean_object* v_n_4558_){
_start:
{
uint8_t v_res_4559_; lean_object* v_r_4560_; 
v_res_4559_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(v_env_4557_, v_n_4558_);
v_r_4560_ = lean_box(v_res_4559_);
return v_r_4560_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4563_; lean_object* v___x_4564_; 
v___f_4563_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_));
v___x_4564_ = l_Lean_registerReservedNamePredicate(v___f_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4565_;
v_res_4565_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4565_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2____boxed(lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
return v_res_4567_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(lean_object* v_thm_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; lean_object* v_env_4572_; lean_object* v_toConstantVal_4573_; lean_object* v_value_4574_; lean_object* v_all_4575_; uint8_t v___y_4577_; lean_object* v_type_4585_; uint8_t v___x_4586_; 
v___x_4571_ = lean_st_ref_get(v___y_4569_);
v_env_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc_ref_n(v_env_4572_, 2);
lean_dec(v___x_4571_);
v_toConstantVal_4573_ = lean_ctor_get(v_thm_4568_, 0);
v_value_4574_ = lean_ctor_get(v_thm_4568_, 1);
v_all_4575_ = lean_ctor_get(v_thm_4568_, 2);
v_type_4585_ = lean_ctor_get(v_toConstantVal_4573_, 2);
v___x_4586_ = l_Lean_Environment_hasUnsafe(v_env_4572_, v_type_4585_);
if (v___x_4586_ == 0)
{
uint8_t v___x_4587_; 
v___x_4587_ = l_Lean_Environment_hasUnsafe(v_env_4572_, v_value_4574_);
v___y_4577_ = v___x_4587_;
goto v___jp_4576_;
}
else
{
lean_dec_ref(v_env_4572_);
v___y_4577_ = v___x_4586_;
goto v___jp_4576_;
}
v___jp_4576_:
{
if (v___y_4577_ == 0)
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_thm_4568_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
else
{
lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
lean_inc(v_all_4575_);
lean_inc_ref(v_value_4574_);
lean_inc_ref(v_toConstantVal_4573_);
lean_dec_ref(v_thm_4568_);
v___x_4580_ = lean_box(0);
v___x_4581_ = 0;
v___x_4582_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4582_, 0, v_toConstantVal_4573_);
lean_ctor_set(v___x_4582_, 1, v_value_4574_);
lean_ctor_set(v___x_4582_, 2, v___x_4580_);
lean_ctor_set(v___x_4582_, 3, v_all_4575_);
lean_ctor_set_uint8(v___x_4582_, sizeof(void*)*4, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_4568_ = stack[0].m_obj;
lean_object* v___y_4569_ = stack[1].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4568_, v___y_4569_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_thm_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4589_, v___y_4590_);
lean_dec(v___y_4590_);
return v_res_4592_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(lean_object* v_thm_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v_thm_4593_, v___y_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_4593_ = stack[0].m_obj;
lean_object* v___y_4594_ = stack[1].m_obj;
lean_object* v___y_4595_ = stack[2].m_obj;
lean_object* v___y_4596_ = stack[3].m_obj;
lean_object* v___y_4597_ = stack[4].m_obj;
lean_object* v_res_4600_;
v_res_4600_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
stack->m_obj
 = v_res_4600_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___boxed(lean_object* v_thm_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1(v_thm_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
return v_res_4607_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_4608_; double v___x_4609_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = lean_float_of_nat(v___x_4608_);
return v___x_4609_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(lean_object* v_cls_4613_, lean_object* v_msg_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_ref_4620_; lean_object* v___x_4621_; lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4667_; 
v_ref_4620_ = lean_ctor_get(v___y_4617_, 2);
v___x_4621_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkHCongrWithArity_spec__0_spec__0(v_msg_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4667_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4667_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v_traceState_4627_; lean_object* v_env_4628_; lean_object* v_nextMacroScope_4629_; lean_object* v_ngen_4630_; lean_object* v_auxDeclNGen_4631_; lean_object* v_cache_4632_; lean_object* v_recordedDeps_4633_; lean_object* v_messages_4634_; lean_object* v_infoState_4635_; lean_object* v_snapshotTasks_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4666_; 
v___x_4626_ = lean_st_ref_take(v___y_4618_);
v_traceState_4627_ = lean_ctor_get(v___x_4626_, 4);
v_env_4628_ = lean_ctor_get(v___x_4626_, 0);
v_nextMacroScope_4629_ = lean_ctor_get(v___x_4626_, 1);
v_ngen_4630_ = lean_ctor_get(v___x_4626_, 2);
v_auxDeclNGen_4631_ = lean_ctor_get(v___x_4626_, 3);
v_cache_4632_ = lean_ctor_get(v___x_4626_, 5);
v_recordedDeps_4633_ = lean_ctor_get(v___x_4626_, 6);
v_messages_4634_ = lean_ctor_get(v___x_4626_, 7);
v_infoState_4635_ = lean_ctor_get(v___x_4626_, 8);
v_snapshotTasks_4636_ = lean_ctor_get(v___x_4626_, 9);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4638_ = v___x_4626_;
v_isShared_4639_ = v_isSharedCheck_4666_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_snapshotTasks_4636_);
lean_inc(v_infoState_4635_);
lean_inc(v_messages_4634_);
lean_inc(v_recordedDeps_4633_);
lean_inc(v_cache_4632_);
lean_inc(v_traceState_4627_);
lean_inc(v_auxDeclNGen_4631_);
lean_inc(v_ngen_4630_);
lean_inc(v_nextMacroScope_4629_);
lean_inc(v_env_4628_);
lean_dec(v___x_4626_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4666_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
uint64_t v_tid_4640_; lean_object* v_traces_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4665_; 
v_tid_4640_ = lean_ctor_get_uint64(v_traceState_4627_, sizeof(void*)*1);
v_traces_4641_ = lean_ctor_get(v_traceState_4627_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_traceState_4627_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4643_ = v_traceState_4627_;
v_isShared_4644_ = v_isSharedCheck_4665_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_traces_4641_);
lean_dec(v_traceState_4627_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4665_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; double v___x_4647_; uint8_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v___x_4645_ = lean_box(0);
v___x_4646_ = lean_box(0);
v___x_4647_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__0);
v___x_4648_ = 0;
v___x_4649_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__1));
v___x_4650_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4650_, 0, v_cls_4613_);
lean_ctor_set(v___x_4650_, 1, v___x_4646_);
lean_ctor_set(v___x_4650_, 2, v___x_4649_);
lean_ctor_set_float(v___x_4650_, sizeof(void*)*3, v___x_4647_);
lean_ctor_set_float(v___x_4650_, sizeof(void*)*3 + 8, v___x_4647_);
lean_ctor_set_uint8(v___x_4650_, sizeof(void*)*3 + 16, v___x_4648_);
v___x_4651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___closed__2));
v___x_4652_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set(v___x_4652_, 1, v_a_4622_);
lean_ctor_set(v___x_4652_, 2, v___x_4651_);
lean_inc(v_ref_4620_);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_ref_4620_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
v___x_4654_ = l_Lean_PersistentArray_push___redArg(v_traces_4641_, v___x_4653_);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 0, v___x_4654_);
v___x_4656_ = v___x_4643_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4654_);
lean_ctor_set_uint64(v_reuseFailAlloc_4664_, sizeof(void*)*1, v_tid_4640_);
v___x_4656_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4658_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 4, v___x_4656_);
v___x_4658_ = v___x_4638_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_env_4628_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_nextMacroScope_4629_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_ngen_4630_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_auxDeclNGen_4631_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4663_, 5, v_cache_4632_);
lean_ctor_set(v_reuseFailAlloc_4663_, 6, v_recordedDeps_4633_);
lean_ctor_set(v_reuseFailAlloc_4663_, 7, v_messages_4634_);
lean_ctor_set(v_reuseFailAlloc_4663_, 8, v_infoState_4635_);
lean_ctor_set(v_reuseFailAlloc_4663_, 9, v_snapshotTasks_4636_);
v___x_4658_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4659_ = lean_st_ref_put(v___y_4618_, v___x_4658_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4645_);
v___x_4661_ = v___x_4624_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4645_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4613_ = stack[0].m_obj;
lean_object* v_msg_4614_ = stack[1].m_obj;
lean_object* v___y_4615_ = stack[2].m_obj;
lean_object* v___y_4616_ = stack[3].m_obj;
lean_object* v___y_4617_ = stack[4].m_obj;
lean_object* v___y_4618_ = stack[5].m_obj;
lean_object* v_res_4668_;
v_res_4668_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4613_, v_msg_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
stack->m_obj
 = v_res_4668_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2___boxed(lean_object* v_cls_4669_, lean_object* v_msg_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v_cls_4669_, v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
return v_res_4676_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
return v___x_4678_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
return v___x_4680_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4684_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4685_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4686_ = l_Lean_Name_append(v___x_4685_, v___x_4684_);
return v___x_4686_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4689_ = l_Lean_stringToMessageData(v___x_4688_);
return v___x_4689_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v_name_4690_, lean_object* v_argKinds_4691_, uint8_t v___x_4692_, lean_object* v___x_4693_, lean_object* v___x_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4739_; lean_object* v_a_4740_; lean_object* v___x_4741_; 
v___x_4739_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__1___redArg(v___x_4694_, v___y_4698_);
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref(v___x_4739_);
v___x_4741_ = l_Lean_addDecl(v_a_4740_, v___x_4692_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_toCold_4742_; lean_object* v_options_4743_; uint8_t v_hasTrace_4744_; 
lean_dec_ref_known(v___x_4741_, 1);
v_toCold_4742_ = lean_ctor_get(v___y_4697_, 0);
v_options_4743_ = lean_ctor_get(v_toCold_4742_, 2);
v_hasTrace_4744_ = lean_ctor_get_uint8(v_options_4743_, sizeof(void*)*1);
if (v_hasTrace_4744_ == 0)
{
goto v___jp_4700_;
}
else
{
lean_object* v_inheritedTraceOptions_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v_inheritedTraceOptions_4745_ = lean_ctor_get(v_toCold_4742_, 11);
v___x_4746_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_4747_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4745_, v_options_4743_, v___x_4747_);
if (v___x_4748_ == 0)
{
goto v___jp_4700_;
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4749_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
lean_inc(v_name_4690_);
v___x_4750_ = l_Lean_MessageData_ofName(v_name_4690_);
v___x_4751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_4753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4751_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_4746_, v___x_4753_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_dec_ref_known(v___x_4754_, 1);
goto v___jp_4700_;
}
else
{
lean_dec_ref(v___x_4693_);
lean_dec_ref(v_argKinds_4691_);
lean_dec(v_name_4690_);
return v___x_4754_;
}
}
}
}
else
{
lean_dec_ref(v___x_4693_);
lean_dec_ref(v_argKinds_4691_);
lean_dec(v_name_4690_);
return v___x_4741_;
}
v___jp_4700_:
{
lean_object* v___x_4701_; lean_object* v_env_4702_; lean_object* v_nextMacroScope_4703_; lean_object* v_ngen_4704_; lean_object* v_auxDeclNGen_4705_; lean_object* v_traceState_4706_; lean_object* v_recordedDeps_4707_; lean_object* v_messages_4708_; lean_object* v_infoState_4709_; lean_object* v_snapshotTasks_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4737_; 
v___x_4701_ = lean_st_ref_take(v___y_4698_);
v_env_4702_ = lean_ctor_get(v___x_4701_, 0);
v_nextMacroScope_4703_ = lean_ctor_get(v___x_4701_, 1);
v_ngen_4704_ = lean_ctor_get(v___x_4701_, 2);
v_auxDeclNGen_4705_ = lean_ctor_get(v___x_4701_, 3);
v_traceState_4706_ = lean_ctor_get(v___x_4701_, 4);
v_recordedDeps_4707_ = lean_ctor_get(v___x_4701_, 6);
v_messages_4708_ = lean_ctor_get(v___x_4701_, 7);
v_infoState_4709_ = lean_ctor_get(v___x_4701_, 8);
v_snapshotTasks_4710_ = lean_ctor_get(v___x_4701_, 9);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4737_ == 0)
{
lean_object* v_unused_4738_; 
v_unused_4738_ = lean_ctor_get(v___x_4701_, 5);
lean_dec(v_unused_4738_);
v___x_4712_ = v___x_4701_;
v_isShared_4713_ = v_isSharedCheck_4737_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_snapshotTasks_4710_);
lean_inc(v_infoState_4709_);
lean_inc(v_messages_4708_);
lean_inc(v_recordedDeps_4707_);
lean_inc(v_traceState_4706_);
lean_inc(v_auxDeclNGen_4705_);
lean_inc(v_ngen_4704_);
lean_inc(v_nextMacroScope_4703_);
lean_inc(v_env_4702_);
lean_dec(v___x_4701_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4737_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4714_ = l_Lean_Meta_congrKindsExt;
v___x_4715_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4714_, v_env_4702_, v_name_4690_, v_argKinds_4691_, v___x_4692_);
v___x_4716_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 5, v___x_4716_);
lean_ctor_set(v___x_4712_, 0, v___x_4715_);
v___x_4718_ = v___x_4712_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_nextMacroScope_4703_);
lean_ctor_set(v_reuseFailAlloc_4736_, 2, v_ngen_4704_);
lean_ctor_set(v_reuseFailAlloc_4736_, 3, v_auxDeclNGen_4705_);
lean_ctor_set(v_reuseFailAlloc_4736_, 4, v_traceState_4706_);
lean_ctor_set(v_reuseFailAlloc_4736_, 5, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4736_, 6, v_recordedDeps_4707_);
lean_ctor_set(v_reuseFailAlloc_4736_, 7, v_messages_4708_);
lean_ctor_set(v_reuseFailAlloc_4736_, 8, v_infoState_4709_);
lean_ctor_set(v_reuseFailAlloc_4736_, 9, v_snapshotTasks_4710_);
v___x_4718_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v_mctx_4721_; lean_object* v_zetaDeltaFVarIds_4722_; lean_object* v_postponed_4723_; lean_object* v_diag_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4734_; 
v___x_4719_ = lean_st_ref_put(v___y_4698_, v___x_4718_);
v___x_4720_ = lean_st_ref_take(v___y_4696_);
v_mctx_4721_ = lean_ctor_get(v___x_4720_, 0);
v_zetaDeltaFVarIds_4722_ = lean_ctor_get(v___x_4720_, 2);
v_postponed_4723_ = lean_ctor_get(v___x_4720_, 3);
v_diag_4724_ = lean_ctor_get(v___x_4720_, 4);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v___x_4720_, 1);
lean_dec(v_unused_4735_);
v___x_4726_ = v___x_4720_;
v_isShared_4727_ = v_isSharedCheck_4734_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_diag_4724_);
lean_inc(v_postponed_4723_);
lean_inc(v_zetaDeltaFVarIds_4722_);
lean_inc(v_mctx_4721_);
lean_dec(v___x_4720_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4734_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4728_; lean_object* v___x_4730_; 
v___x_4728_ = lean_box(0);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 1, v___x_4693_);
v___x_4730_ = v___x_4726_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_mctx_4721_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4733_, 2, v_zetaDeltaFVarIds_4722_);
lean_ctor_set(v_reuseFailAlloc_4733_, 3, v_postponed_4723_);
lean_ctor_set(v_reuseFailAlloc_4733_, 4, v_diag_4724_);
v___x_4730_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_st_ref_put(v___y_4696_, v___x_4730_);
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4728_);
return v___x_4732_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4690_ = stack[0].m_obj;
lean_object* v_argKinds_4691_ = stack[1].m_obj;
uint8_t v___x_4692_ = stack[2].m_num;
lean_object* v___x_4693_ = stack[3].m_obj;
lean_object* v___x_4694_ = stack[4].m_obj;
lean_object* v___y_4695_ = stack[5].m_obj;
lean_object* v___y_4696_ = stack[6].m_obj;
lean_object* v___y_4697_ = stack[7].m_obj;
lean_object* v___y_4698_ = stack[8].m_obj;
lean_object* v_res_4755_;
v_res_4755_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4690_, v_argKinds_4691_, v___x_4692_, v___x_4693_, v___x_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
stack->m_obj
 = v_res_4755_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_name_4756_, lean_object* v_argKinds_4757_, lean_object* v___x_4758_, lean_object* v___x_4759_, lean_object* v___x_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
uint8_t v___x_12076__boxed_4766_; lean_object* v_res_4767_; 
v___x_12076__boxed_4766_ = lean_unbox(v___x_4758_);
v_res_4767_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v_name_4756_, v_argKinds_4757_, v___x_12076__boxed_4766_, v___x_4759_, v___x_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
if (lean_obj_tag(v_a_4768_) == 0)
{
lean_object* v___x_4770_; 
v___x_4770_ = l_List_reverse___redArg(v_a_4769_);
return v___x_4770_;
}
else
{
lean_object* v_head_4771_; lean_object* v_tail_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4781_; 
v_head_4771_ = lean_ctor_get(v_a_4768_, 0);
v_tail_4772_ = lean_ctor_get(v_a_4768_, 1);
v_isSharedCheck_4781_ = !lean_is_exclusive(v_a_4768_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4774_ = v_a_4768_;
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_tail_4772_);
lean_inc(v_head_4771_);
lean_dec(v_a_4768_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4778_; 
v___x_4776_ = l_Lean_mkLevelParam(v_head_4771_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 1, v_a_4769_);
lean_ctor_set(v___x_4774_, 0, v___x_4776_);
v___x_4778_ = v___x_4774_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4776_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_a_4769_);
v___x_4778_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
v_a_4768_ = v_tail_4772_;
v_a_4769_ = v___x_4778_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4784_ = lean_box(1);
v___x_4785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4786_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
lean_ctor_set(v___x_4787_, 1, v___x_4785_);
lean_ctor_set(v___x_4787_, 2, v___x_4784_);
return v___x_4787_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4790_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4791_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
lean_ctor_set(v___x_4793_, 2, v___x_4792_);
lean_ctor_set(v___x_4793_, 3, v___x_4792_);
lean_ctor_set(v___x_4793_, 4, v___x_4791_);
lean_ctor_set(v___x_4793_, 5, v___x_4791_);
lean_ctor_set(v___x_4793_, 6, v___x_4791_);
lean_ctor_set(v___x_4793_, 7, v___x_4791_);
lean_ctor_set(v___x_4793_, 8, v___x_4791_);
lean_ctor_set(v___x_4793_, 9, v___x_4791_);
lean_ctor_set(v___x_4793_, 10, v___x_4791_);
lean_ctor_set(v___x_4793_, 11, v___x_4790_);
return v___x_4793_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4795_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
lean_ctor_set(v___x_4795_, 2, v___x_4794_);
lean_ctor_set(v___x_4795_, 3, v___x_4794_);
lean_ctor_set(v___x_4795_, 4, v___x_4794_);
lean_ctor_set(v___x_4795_, 5, v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
lean_ctor_set(v___x_4797_, 2, v___x_4796_);
lean_ctor_set(v___x_4797_, 3, v___x_4796_);
lean_ctor_set(v___x_4797_, 4, v___x_4796_);
return v___x_4797_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(lean_object* v___x_4798_, lean_object* v_name_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
if (lean_obj_tag(v_name_4799_) == 1)
{
lean_object* v_pre_4803_; lean_object* v_str_4804_; lean_object* v___x_4805_; lean_object* v_env_4806_; uint8_t v___x_4807_; uint8_t v___x_4808_; 
v_pre_4803_ = lean_ctor_get(v_name_4799_, 0);
lean_inc_n(v_pre_4803_, 2);
v_str_4804_ = lean_ctor_get(v_name_4799_, 1);
v___x_4805_ = lean_st_ref_get(v___y_4801_);
v_env_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc_ref(v_env_4806_);
lean_dec(v___x_4805_);
v___x_4807_ = 1;
v___x_4808_ = l_Lean_Environment_contains(v_env_4806_, v_pre_4803_, v___x_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
lean_dec(v_pre_4803_);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v___x_4798_);
v___x_4809_ = lean_box(v___x_4808_);
v___x_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4809_);
return v___x_4810_;
}
else
{
uint8_t v___x_4811_; lean_object* v___y_4813_; uint8_t v___y_4814_; lean_object* v_a_4819_; 
lean_inc_ref(v_str_4804_);
v___x_4811_ = l_Lean_Meta_isHCongrReservedNameSuffix(v_str_4804_);
if (v___x_4811_ == 0)
{
lean_object* v___x_4822_; uint8_t v___x_4823_; 
v___x_4822_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v___x_4823_ = lean_string_dec_eq(v_str_4804_, v___x_4822_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec(v_pre_4803_);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v___x_4798_);
v___x_4824_ = lean_box(v___x_4823_);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
else
{
uint8_t v___x_4826_; uint8_t v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; uint64_t v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; uint8_t v_a_4844_; lean_object* v___x_4848_; 
v___x_4826_ = 1;
v___x_4827_ = 0;
v___x_4828_ = 2;
v___x_4829_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4829_, 0, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 1, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 2, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 3, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 4, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 5, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 6, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 7, v___x_4811_);
lean_ctor_set_uint8(v___x_4829_, 8, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 9, v___x_4826_);
lean_ctor_set_uint8(v___x_4829_, 10, v___x_4827_);
lean_ctor_set_uint8(v___x_4829_, 11, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 12, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 13, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 14, v___x_4828_);
lean_ctor_set_uint8(v___x_4829_, 15, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 16, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 17, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 18, v___x_4823_);
lean_ctor_set_uint8(v___x_4829_, 19, v___x_4811_);
v___x_4830_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4829_);
v___x_4831_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set_uint64(v___x_4831_, sizeof(void*)*1, v___x_4830_);
v___x_4832_ = lean_unsigned_to_nat(0u);
v___x_4833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4834_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4835_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4836_ = lean_box(0);
lean_inc(v___x_4798_);
v___x_4837_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4837_, 0, v___x_4831_);
lean_ctor_set(v___x_4837_, 1, v___x_4798_);
lean_ctor_set(v___x_4837_, 2, v___x_4834_);
lean_ctor_set(v___x_4837_, 3, v___x_4835_);
lean_ctor_set(v___x_4837_, 4, v___x_4836_);
lean_ctor_set(v___x_4837_, 5, v___x_4832_);
lean_ctor_set(v___x_4837_, 6, v___x_4836_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7, v___x_4811_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 1, v___x_4811_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 2, v___x_4811_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 3, v___x_4807_);
v___x_4838_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4839_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4840_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4838_);
lean_ctor_set(v___x_4841_, 1, v___x_4839_);
lean_ctor_set(v___x_4841_, 2, v___x_4798_);
lean_ctor_set(v___x_4841_, 3, v___x_4833_);
lean_ctor_set(v___x_4841_, 4, v___x_4840_);
v___x_4842_ = lean_st_mk_ref(v___x_4841_);
lean_inc(v_pre_4803_);
v___x_4848_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4803_, v___x_4837_, v___x_4842_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v___x_4850_ = l_Lean_ConstantInfo_levelParams(v_a_4849_);
lean_dec(v_a_4849_);
v___x_4851_ = lean_box(0);
lean_inc(v___x_4850_);
v___x_4852_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4850_, v___x_4851_);
lean_inc(v_pre_4803_);
v___x_4853_ = l_Lean_mkConst(v_pre_4803_, v___x_4852_);
lean_inc_ref(v___x_4853_);
v___x_4854_ = l_Lean_Meta_getFunInfo(v___x_4853_, v___x_4836_, v___x_4837_, v___x_4842_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4856_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
lean_inc_ref(v___x_4853_);
v___x_4856_ = l_Lean_Meta_getCongrSimpKinds(v___x_4853_, v_a_4855_, v___x_4837_, v___x_4842_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4858_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_a_4857_);
lean_dec_ref_known(v___x_4856_, 1);
v___x_4858_ = l_Lean_Meta_mkCongrSimpCore_x3f(v___x_4853_, v_a_4855_, v_a_4857_, v___x_4807_, v___x_4837_, v___x_4842_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
if (lean_obj_tag(v_a_4859_) == 1)
{
lean_object* v_val_4860_; lean_object* v_type_4861_; lean_object* v_proof_4862_; lean_object* v_argKinds_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4876_; 
v_val_4860_ = lean_ctor_get(v_a_4859_, 0);
lean_inc(v_val_4860_);
lean_dec_ref_known(v_a_4859_, 1);
v_type_4861_ = lean_ctor_get(v_val_4860_, 0);
v_proof_4862_ = lean_ctor_get(v_val_4860_, 1);
v_argKinds_4863_ = lean_ctor_get(v_val_4860_, 2);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_val_4860_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4865_ = v_val_4860_;
v_isShared_4866_ = v_isSharedCheck_4876_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_argKinds_4863_);
lean_inc(v_proof_4862_);
lean_inc(v_type_4861_);
lean_dec(v_val_4860_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4876_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
lean_inc_ref(v_name_4799_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 2, v_type_4861_);
lean_ctor_set(v___x_4865_, 1, v___x_4850_);
lean_ctor_set(v___x_4865_, 0, v_name_4799_);
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_name_4799_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v___x_4850_);
lean_ctor_set(v_reuseFailAlloc_4875_, 2, v_type_4861_);
v___x_4868_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___f_4872_; lean_object* v___x_4873_; 
lean_inc_ref_n(v_name_4799_, 2);
v___x_4869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4869_, 0, v_name_4799_);
lean_ctor_set(v___x_4869_, 1, v___x_4851_);
v___x_4870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v_proof_4862_);
lean_ctor_set(v___x_4870_, 2, v___x_4869_);
v___x_4871_ = lean_box(v___x_4811_);
v___f_4872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4872_, 0, v_name_4799_);
lean_closure_set(v___f_4872_, 1, v_argKinds_4863_);
lean_closure_set(v___f_4872_, 2, v___x_4871_);
lean_closure_set(v___f_4872_, 3, v___x_4839_);
lean_closure_set(v___f_4872_, 4, v___x_4870_);
v___x_4873_ = l_Lean_Meta_realizeConst(v_pre_4803_, v_name_4799_, v___f_4872_, v___x_4837_, v___x_4842_, v___y_4800_, v___y_4801_);
lean_dec_ref_known(v___x_4837_, 7);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_dec_ref_known(v___x_4873_, 1);
v_a_4844_ = v___x_4807_;
goto v___jp_4843_;
}
else
{
lean_object* v_a_4874_; 
lean_dec(v___x_4842_);
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4873_, 1);
v_a_4819_ = v_a_4874_;
goto v___jp_4818_;
}
}
}
}
else
{
lean_dec(v_a_4859_);
lean_dec(v___x_4850_);
lean_dec_ref_known(v___x_4837_, 7);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v_pre_4803_);
v_a_4844_ = v___x_4811_;
goto v___jp_4843_;
}
}
else
{
lean_object* v_a_4877_; 
lean_dec(v___x_4850_);
lean_dec(v___x_4842_);
lean_dec_ref_known(v___x_4837_, 7);
lean_dec(v_pre_4803_);
lean_dec_ref_known(v_name_4799_, 2);
v_a_4877_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v___x_4858_, 1);
v_a_4819_ = v_a_4877_;
goto v___jp_4818_;
}
}
else
{
lean_object* v_a_4878_; 
lean_dec(v_a_4855_);
lean_dec_ref(v___x_4853_);
lean_dec(v___x_4850_);
lean_dec(v___x_4842_);
lean_dec_ref_known(v___x_4837_, 7);
lean_dec(v_pre_4803_);
lean_dec_ref_known(v_name_4799_, 2);
v_a_4878_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4856_, 1);
v_a_4819_ = v_a_4878_;
goto v___jp_4818_;
}
}
else
{
lean_object* v_a_4879_; 
lean_dec_ref(v___x_4853_);
lean_dec(v___x_4850_);
lean_dec(v___x_4842_);
lean_dec_ref_known(v___x_4837_, 7);
lean_dec(v_pre_4803_);
lean_dec_ref_known(v_name_4799_, 2);
v_a_4879_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4854_, 1);
v_a_4819_ = v_a_4879_;
goto v___jp_4818_;
}
}
else
{
lean_object* v_a_4880_; 
lean_dec(v___x_4842_);
lean_dec_ref_known(v___x_4837_, 7);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v_pre_4803_);
v_a_4880_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4848_, 1);
v_a_4819_ = v_a_4880_;
goto v___jp_4818_;
}
v___jp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4845_ = lean_st_ref_get(v___x_4842_);
lean_dec(v___x_4842_);
lean_dec(v___x_4845_);
v___x_4846_ = lean_box(v_a_4844_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
return v___x_4847_;
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; uint8_t v___x_4888_; lean_object* v___y_4890_; uint8_t v___y_4891_; lean_object* v_a_4896_; uint8_t v___x_4899_; uint8_t v___x_4900_; uint8_t v___x_4901_; lean_object* v___x_4902_; uint64_t v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4881_ = lean_unsigned_to_nat(7u);
v___x_4882_ = lean_unsigned_to_nat(0u);
v___x_4883_ = lean_string_utf8_byte_size(v_str_4804_);
lean_inc_ref_n(v_str_4804_, 2);
v___x_4884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4884_, 0, v_str_4804_);
lean_ctor_set(v___x_4884_, 1, v___x_4882_);
lean_ctor_set(v___x_4884_, 2, v___x_4883_);
v___x_4885_ = l_String_Slice_Pos_nextn(v___x_4884_, v___x_4882_, v___x_4881_);
lean_dec_ref_known(v___x_4884_, 3);
v___x_4886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4886_, 0, v_str_4804_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
lean_ctor_set(v___x_4886_, 2, v___x_4883_);
v___x_4887_ = l_String_Slice_toNat_x21(v___x_4886_);
lean_dec_ref_known(v___x_4886_, 3);
v___x_4888_ = 0;
v___x_4899_ = 1;
v___x_4900_ = 0;
v___x_4901_ = 2;
v___x_4902_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4902_, 0, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 1, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 2, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 3, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 4, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 5, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 6, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 7, v___x_4888_);
lean_ctor_set_uint8(v___x_4902_, 8, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 9, v___x_4899_);
lean_ctor_set_uint8(v___x_4902_, 10, v___x_4900_);
lean_ctor_set_uint8(v___x_4902_, 11, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 12, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 13, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 14, v___x_4901_);
lean_ctor_set_uint8(v___x_4902_, 15, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 16, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 17, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 18, v___x_4811_);
lean_ctor_set_uint8(v___x_4902_, 19, v___x_4888_);
v___x_4903_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4902_);
v___x_4904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set_uint64(v___x_4904_, sizeof(void*)*1, v___x_4903_);
v___x_4905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4906_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4907_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4908_ = lean_box(0);
lean_inc(v___x_4798_);
v___x_4909_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4909_, 0, v___x_4904_);
lean_ctor_set(v___x_4909_, 1, v___x_4798_);
lean_ctor_set(v___x_4909_, 2, v___x_4906_);
lean_ctor_set(v___x_4909_, 3, v___x_4907_);
lean_ctor_set(v___x_4909_, 4, v___x_4908_);
lean_ctor_set(v___x_4909_, 5, v___x_4882_);
lean_ctor_set(v___x_4909_, 6, v___x_4908_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*7, v___x_4888_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*7 + 1, v___x_4888_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*7 + 2, v___x_4888_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*7 + 3, v___x_4807_);
v___x_4910_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4911_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4912_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_4913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4910_);
lean_ctor_set(v___x_4913_, 1, v___x_4911_);
lean_ctor_set(v___x_4913_, 2, v___x_4798_);
lean_ctor_set(v___x_4913_, 3, v___x_4905_);
lean_ctor_set(v___x_4913_, 4, v___x_4912_);
v___x_4914_ = lean_st_mk_ref(v___x_4913_);
lean_inc(v_pre_4803_);
v___x_4915_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_getClassSubobjectMask_x3f_spec__0(v_pre_4803_, v___x_4909_, v___x_4914_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = l_Lean_ConstantInfo_levelParams(v_a_4916_);
lean_dec(v_a_4916_);
v___x_4918_ = lean_box(0);
lean_inc(v___x_4917_);
v___x_4919_ = l_List_mapTR_loop___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__0(v___x_4917_, v___x_4918_);
lean_inc(v_pre_4803_);
v___x_4920_ = l_Lean_mkConst(v_pre_4803_, v___x_4919_);
v___x_4921_ = l_Lean_Meta_mkHCongrWithArity(v___x_4920_, v___x_4887_, v___x_4909_, v___x_4914_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v_type_4923_; lean_object* v_proof_4924_; lean_object* v_argKinds_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4948_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
v_type_4923_ = lean_ctor_get(v_a_4922_, 0);
v_proof_4924_ = lean_ctor_get(v_a_4922_, 1);
v_argKinds_4925_ = lean_ctor_get(v_a_4922_, 2);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_a_4922_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4927_ = v_a_4922_;
v_isShared_4928_ = v_isSharedCheck_4948_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_argKinds_4925_);
lean_inc(v_proof_4924_);
lean_inc(v_type_4923_);
lean_dec(v_a_4922_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4948_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
lean_inc_ref(v_name_4799_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 2, v_type_4923_);
lean_ctor_set(v___x_4927_, 1, v___x_4917_);
lean_ctor_set(v___x_4927_, 0, v_name_4799_);
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_name_4799_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4917_);
lean_ctor_set(v_reuseFailAlloc_4947_, 2, v_type_4923_);
v___x_4930_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___f_4934_; lean_object* v___x_4935_; 
lean_inc_ref_n(v_name_4799_, 2);
v___x_4931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4931_, 0, v_name_4799_);
lean_ctor_set(v___x_4931_, 1, v___x_4918_);
v___x_4932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4930_);
lean_ctor_set(v___x_4932_, 1, v_proof_4924_);
lean_ctor_set(v___x_4932_, 2, v___x_4931_);
v___x_4933_ = lean_box(v___x_4888_);
v___f_4934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed), 10, 5);
lean_closure_set(v___f_4934_, 0, v_name_4799_);
lean_closure_set(v___f_4934_, 1, v_argKinds_4925_);
lean_closure_set(v___f_4934_, 2, v___x_4933_);
lean_closure_set(v___f_4934_, 3, v___x_4911_);
lean_closure_set(v___f_4934_, 4, v___x_4932_);
v___x_4935_ = l_Lean_Meta_realizeConst(v_pre_4803_, v_name_4799_, v___f_4934_, v___x_4909_, v___x_4914_, v___y_4800_, v___y_4801_);
lean_dec_ref_known(v___x_4909_, 7);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4944_; 
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4935_);
if (v_isSharedCheck_4944_ == 0)
{
lean_object* v_unused_4945_; 
v_unused_4945_ = lean_ctor_get(v___x_4935_, 0);
lean_dec(v_unused_4945_);
v___x_4937_ = v___x_4935_;
v_isShared_4938_ = v_isSharedCheck_4944_;
goto v_resetjp_4936_;
}
else
{
lean_dec(v___x_4935_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4944_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4939_ = lean_st_ref_get(v___x_4914_);
lean_dec(v___x_4914_);
lean_dec(v___x_4939_);
v___x_4940_ = lean_box(v___x_4807_);
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v___x_4940_);
v___x_4942_ = v___x_4937_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
else
{
lean_object* v_a_4946_; 
lean_dec(v___x_4914_);
v_a_4946_ = lean_ctor_get(v___x_4935_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___x_4935_, 1);
v_a_4896_ = v_a_4946_;
goto v___jp_4895_;
}
}
}
}
else
{
lean_object* v_a_4949_; 
lean_dec(v___x_4917_);
lean_dec(v___x_4914_);
lean_dec_ref_known(v___x_4909_, 7);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v_pre_4803_);
v_a_4949_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___x_4921_, 1);
v_a_4896_ = v_a_4949_;
goto v___jp_4895_;
}
}
else
{
lean_object* v_a_4950_; 
lean_dec(v___x_4914_);
lean_dec_ref_known(v___x_4909_, 7);
lean_dec(v___x_4887_);
lean_dec_ref_known(v_name_4799_, 2);
lean_dec(v_pre_4803_);
v_a_4950_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4915_, 1);
v_a_4896_ = v_a_4950_;
goto v___jp_4895_;
}
v___jp_4889_:
{
if (v___y_4891_ == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref(v___y_4890_);
v___x_4892_ = lean_box(v___x_4888_);
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
return v___x_4893_;
}
else
{
lean_object* v___x_4894_; 
v___x_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___y_4890_);
return v___x_4894_;
}
}
v___jp_4895_:
{
uint8_t v___x_4897_; 
v___x_4897_ = l_Lean_Exception_isInterrupt(v_a_4896_);
if (v___x_4897_ == 0)
{
uint8_t v___x_4898_; 
lean_inc_ref(v_a_4896_);
v___x_4898_ = l_Lean_Exception_isRuntime(v_a_4896_);
v___y_4890_ = v_a_4896_;
v___y_4891_ = v___x_4898_;
goto v___jp_4889_;
}
else
{
v___y_4890_ = v_a_4896_;
v___y_4891_ = v___x_4897_;
goto v___jp_4889_;
}
}
}
v___jp_4812_:
{
if (v___y_4814_ == 0)
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec_ref(v___y_4813_);
v___x_4815_ = lean_box(v___x_4811_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
else
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v___y_4813_);
return v___x_4817_;
}
}
v___jp_4818_:
{
uint8_t v___x_4820_; 
v___x_4820_ = l_Lean_Exception_isInterrupt(v_a_4819_);
if (v___x_4820_ == 0)
{
uint8_t v___x_4821_; 
lean_inc_ref(v_a_4819_);
v___x_4821_ = l_Lean_Exception_isRuntime(v_a_4819_);
v___y_4813_ = v_a_4819_;
v___y_4814_ = v___x_4821_;
goto v___jp_4812_;
}
else
{
v___y_4813_ = v_a_4819_;
v___y_4814_ = v___x_4820_;
goto v___jp_4812_;
}
}
}
}
else
{
uint8_t v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec(v_name_4799_);
lean_dec(v___x_4798_);
v___x_4951_ = 0;
v___x_4952_ = lean_box(v___x_4951_);
v___x_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4952_);
return v___x_4953_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4798_ = stack[0].m_obj;
lean_object* v_name_4799_ = stack[1].m_obj;
lean_object* v___y_4800_ = stack[2].m_obj;
lean_object* v___y_4801_ = stack[3].m_obj;
lean_object* v_res_4954_;
v_res_4954_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4798_, v_name_4799_, v___y_4800_, v___y_4801_);
stack->m_obj
 = v_res_4954_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v___x_4955_, lean_object* v_name_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(v___x_4955_, v_name_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
return v_res_4960_;
}
}
lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4964_; lean_object* v___x_4965_; 
v___f_4964_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_));
v___x_4965_ = l_Lean_registerReservedNameAction(v___f_4964_);
return v___x_4965_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4966_;
v_res_4966_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4966_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2____boxed(lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
return v_res_4968_;
}
}
lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(lean_object* v_msg_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v___f_4975_; lean_object* v___x_1735__overap_4976_; lean_object* v___x_4977_; 
v___f_4975_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go_spec__0___closed__0));
v___x_1735__overap_4976_ = lean_panic_fn_borrowed(v___f_4975_, v_msg_4969_);
lean_inc(v___y_4973_);
lean_inc_ref(v___y_4972_);
lean_inc(v___y_4971_);
lean_inc_ref(v___y_4970_);
v___x_4977_ = lean_apply_5(v___x_1735__overap_4976_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, lean_box(0));
return v___x_4977_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4969_ = stack[0].m_obj;
lean_object* v___y_4970_ = stack[1].m_obj;
lean_object* v___y_4971_ = stack[2].m_obj;
lean_object* v___y_4972_ = stack[3].m_obj;
lean_object* v___y_4973_ = stack[4].m_obj;
lean_object* v_res_4978_;
v_res_4978_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
stack->m_obj
 = v_res_4978_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0___boxed(lean_object* v_msg_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v_msg_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
return v_res_4985_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4987_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_4988_ = lean_unsigned_to_nat(8u);
v___x_4989_ = lean_unsigned_to_nat(461u);
v___x_4990_ = ((lean_object*)(l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__0));
v___x_4991_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_4992_ = l_mkPanicMessageWithDecl(v___x_4991_, v___x_4990_, v___x_4989_, v___x_4988_, v___x_4987_);
return v___x_4992_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(lean_object* v_thmName_4993_, lean_object* v_levels_4994_, lean_object* v___x_4995_, lean_object* v_____r_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
lean_inc(v_thmName_4993_);
v___x_5002_ = l_Lean_mkConst(v_thmName_4993_, v_levels_4994_);
lean_inc(v___y_5000_);
lean_inc_ref(v___y_4999_);
lean_inc(v___y_4998_);
lean_inc_ref(v___y_4997_);
lean_inc_ref(v___x_5002_);
v___x_5003_ = lean_infer_type(v___x_5002_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5047_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5047_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5047_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5008_; lean_object* v_env_5009_; lean_object* v___x_5010_; lean_object* v_toEnvExtension_5011_; lean_object* v_asyncMode_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; 
v___x_5008_ = lean_st_ref_get(v___y_5000_);
v_env_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc_ref(v_env_5009_);
lean_dec(v___x_5008_);
v___x_5010_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_5011_ = lean_ctor_get(v___x_5010_, 0);
v_asyncMode_5012_ = lean_ctor_get(v_toEnvExtension_5011_, 2);
v___x_5013_ = 0;
v___x_5014_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4995_, v___x_5010_, v_env_5009_, v_thmName_4993_, v_asyncMode_5012_, v___x_5013_);
if (lean_obj_tag(v___x_5014_) == 1)
{
lean_object* v_val_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5027_; 
v_val_5015_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5017_ = v___x_5014_;
v_isShared_5018_ = v_isSharedCheck_5027_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_val_5015_);
lean_dec(v___x_5014_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5027_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5019_, 0, v_a_5004_);
lean_ctor_set(v___x_5019_, 1, v___x_5002_);
lean_ctor_set(v___x_5019_, 2, v_val_5015_);
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 0, v___x_5019_);
v___x_5021_ = v___x_5017_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5022_);
v___x_5024_ = v___x_5006_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
lean_dec(v___x_5014_);
lean_del_object(v___x_5006_);
lean_dec(v_a_5004_);
lean_dec_ref(v___x_5002_);
v___x_5028_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___closed__1);
v___x_5029_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_5028_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5038_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5032_ = v___x_5029_;
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5029_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5034_, 0, v_a_5030_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 0, v___x_5034_);
v___x_5036_ = v___x_5032_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
v_a_5039_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5029_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5029_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
}
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec_ref(v___x_5002_);
lean_dec_ref(v___x_4995_);
lean_dec(v_thmName_4993_);
v_a_5048_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5003_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5003_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_4993_ = stack[0].m_obj;
lean_object* v_levels_4994_ = stack[1].m_obj;
lean_object* v___x_4995_ = stack[2].m_obj;
lean_object* v_____r_4996_ = stack[3].m_obj;
lean_object* v___y_4997_ = stack[4].m_obj;
lean_object* v___y_4998_ = stack[5].m_obj;
lean_object* v___y_4999_ = stack[6].m_obj;
lean_object* v___y_5000_ = stack[7].m_obj;
lean_object* v_res_5056_;
v_res_5056_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_4993_, v_levels_4994_, v___x_4995_, v_____r_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
stack->m_obj
 = v_res_5056_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0___boxed(lean_object* v_thmName_5057_, lean_object* v_levels_5058_, lean_object* v___x_5059_, lean_object* v_____r_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_5057_, v_levels_5058_, v___x_5059_, v_____r_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
return v_res_5066_;
}
}
static lean_object* _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0(void){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Array_instInhabited___redArg();
return v___x_5067_;
}
}
lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f(lean_object* v_declName_5068_, lean_object* v_levels_5069_, lean_object* v_numArgs_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_){
_start:
{
lean_object* v___y_5077_; uint8_t v___y_5078_; lean_object* v_a_5083_; lean_object* v___y_5087_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v_suffix_5101_; lean_object* v_thmName_5102_; lean_object* v___x_5103_; lean_object* v_env_5104_; uint8_t v___x_5105_; 
v___x_5098_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5099_ = ((lean_object*)(l_Lean_Meta_hcongrThmSuffixBasePrefix___closed__0));
v___x_5100_ = l_Nat_reprFast(v_numArgs_5070_);
v_suffix_5101_ = lean_string_append(v___x_5099_, v___x_5100_);
lean_dec_ref(v___x_5100_);
v_thmName_5102_ = l_Lean_Name_str___override(v_declName_5068_, v_suffix_5101_);
v___x_5103_ = lean_st_ref_get(v_a_5074_);
v_env_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc_ref(v_env_5104_);
lean_dec(v___x_5103_);
v___x_5105_ = l_Lean_Environment_containsOnBranch(v_env_5104_, v_thmName_5102_);
lean_dec_ref(v_env_5104_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_inc(v_thmName_5102_);
v___x_5106_ = l_Lean_executeReservedNameAction(v_thmName_5102_, v_a_5073_, v_a_5074_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
lean_dec_ref_known(v___x_5106_, 1);
v___x_5107_ = lean_box(0);
v___x_5108_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_5102_, v_levels_5069_, v___x_5098_, v___x_5107_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
v___y_5087_ = v___x_5108_;
goto v___jp_5086_;
}
else
{
lean_object* v_a_5109_; 
lean_dec(v_thmName_5102_);
lean_dec(v_levels_5069_);
v_a_5109_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5106_, 1);
v_a_5083_ = v_a_5109_;
goto v___jp_5082_;
}
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = lean_box(0);
v___x_5111_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f___lam__0(v_thmName_5102_, v_levels_5069_, v___x_5098_, v___x_5110_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
v___y_5087_ = v___x_5111_;
goto v___jp_5086_;
}
v___jp_5076_:
{
if (v___y_5078_ == 0)
{
lean_object* v___x_5079_; lean_object* v___x_5080_; 
lean_dec_ref(v___y_5077_);
v___x_5079_ = lean_box(0);
v___x_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
return v___x_5080_;
}
else
{
lean_object* v___x_5081_; 
v___x_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5081_, 0, v___y_5077_);
return v___x_5081_;
}
}
v___jp_5082_:
{
uint8_t v___x_5084_; 
v___x_5084_ = l_Lean_Exception_isInterrupt(v_a_5083_);
if (v___x_5084_ == 0)
{
uint8_t v___x_5085_; 
lean_inc_ref(v_a_5083_);
v___x_5085_ = l_Lean_Exception_isRuntime(v_a_5083_);
v___y_5077_ = v_a_5083_;
v___y_5078_ = v___x_5085_;
goto v___jp_5076_;
}
else
{
v___y_5077_ = v_a_5083_;
v___y_5078_ = v___x_5084_;
goto v___jp_5076_;
}
}
v___jp_5086_:
{
if (lean_obj_tag(v___y_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5096_; 
v_a_5088_ = lean_ctor_get(v___y_5087_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___y_5087_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5090_ = v___y_5087_;
v_isShared_5091_ = v_isSharedCheck_5096_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___y_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5096_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v_a_5092_; lean_object* v___x_5094_; 
v_a_5092_ = lean_ctor_get(v_a_5088_, 0);
lean_inc(v_a_5092_);
lean_dec(v_a_5088_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v_a_5092_);
v___x_5094_ = v___x_5090_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5092_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
else
{
lean_object* v_a_5097_; 
v_a_5097_ = lean_ctor_get(v___y_5087_, 0);
lean_inc(v_a_5097_);
lean_dec_ref_known(v___y_5087_, 1);
v_a_5083_ = v_a_5097_;
goto v___jp_5082_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkHCongrWithArityForConst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5068_ = stack[0].m_obj;
lean_object* v_levels_5069_ = stack[1].m_obj;
lean_object* v_numArgs_5070_ = stack[2].m_obj;
lean_object* v_a_5071_ = stack[3].m_obj;
lean_object* v_a_5072_ = stack[4].m_obj;
lean_object* v_a_5073_ = stack[5].m_obj;
lean_object* v_a_5074_ = stack[6].m_obj;
lean_object* v_res_5112_;
v_res_5112_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_5068_, v_levels_5069_, v_numArgs_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
stack->m_obj
 = v_res_5112_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHCongrWithArityForConst_x3f___boxed(lean_object* v_declName_5113_, lean_object* v_levels_5114_, lean_object* v_numArgs_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Meta_mkHCongrWithArityForConst_x3f(v_declName_5113_, v_levels_5114_, v_numArgs_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
return v_res_5121_;
}
}
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(lean_object* v_____r_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5130_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___closed__0));
v___x_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
return v___x_5131_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_5124_ = stack[0].m_obj;
lean_object* v___y_5125_ = stack[1].m_obj;
lean_object* v___y_5126_ = stack[2].m_obj;
lean_object* v___y_5127_ = stack[3].m_obj;
lean_object* v___y_5128_ = stack[4].m_obj;
lean_object* v_res_5132_;
v_res_5132_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
stack->m_obj
 = v_res_5132_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0___boxed(lean_object* v_____r_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_____r_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
return v_res_5139_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5141_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__2));
v___x_5142_ = lean_unsigned_to_nat(8u);
v___x_5143_ = lean_unsigned_to_nat(478u);
v___x_5144_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__0));
v___x_5145_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCongrSimpCore_x3f_mkProof_go___closed__0));
v___x_5146_ = l_mkPanicMessageWithDecl(v___x_5145_, v___x_5144_, v___x_5143_, v___x_5142_, v___x_5141_);
return v___x_5146_;
}
}
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(lean_object* v_thmName_5147_, lean_object* v_levels_5148_, lean_object* v___x_5149_, lean_object* v_____r_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
lean_inc(v_thmName_5147_);
v___x_5156_ = l_Lean_mkConst(v_thmName_5147_, v_levels_5148_);
lean_inc(v___y_5154_);
lean_inc_ref(v___y_5153_);
lean_inc(v___y_5152_);
lean_inc_ref(v___y_5151_);
lean_inc_ref(v___x_5156_);
v___x_5157_ = lean_infer_type(v___x_5156_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5201_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5160_ = v___x_5157_;
v_isShared_5161_ = v_isSharedCheck_5201_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_a_5158_);
lean_dec(v___x_5157_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5201_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5162_; lean_object* v_env_5163_; lean_object* v___x_5164_; lean_object* v_toEnvExtension_5165_; lean_object* v_asyncMode_5166_; uint8_t v___x_5167_; lean_object* v___x_5168_; 
v___x_5162_ = lean_st_ref_get(v___y_5154_);
v_env_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc_ref(v_env_5163_);
lean_dec(v___x_5162_);
v___x_5164_ = l_Lean_Meta_congrKindsExt;
v_toEnvExtension_5165_ = lean_ctor_get(v___x_5164_, 0);
v_asyncMode_5166_ = lean_ctor_get(v_toEnvExtension_5165_, 2);
v___x_5167_ = 0;
v___x_5168_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_5149_, v___x_5164_, v_env_5163_, v_thmName_5147_, v_asyncMode_5166_, v___x_5167_);
if (lean_obj_tag(v___x_5168_) == 1)
{
lean_object* v_val_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5181_; 
v_val_5169_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5171_ = v___x_5168_;
v_isShared_5172_ = v_isSharedCheck_5181_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_val_5169_);
lean_dec(v___x_5168_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5181_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5173_; lean_object* v___x_5175_; 
v___x_5173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5173_, 0, v_a_5158_);
lean_ctor_set(v___x_5173_, 1, v___x_5156_);
lean_ctor_set(v___x_5173_, 2, v_val_5169_);
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 0, v___x_5173_);
v___x_5175_ = v___x_5171_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5173_);
v___x_5175_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
lean_object* v___x_5176_; lean_object* v___x_5178_; 
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
if (v_isShared_5161_ == 0)
{
lean_ctor_set(v___x_5160_, 0, v___x_5176_);
v___x_5178_ = v___x_5160_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec(v___x_5168_);
lean_del_object(v___x_5160_);
lean_dec(v_a_5158_);
lean_dec_ref(v___x_5156_);
v___x_5182_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___closed__1);
v___x_5183_ = l_panic___at___00Lean_Meta_mkHCongrWithArityForConst_x3f_spec__0(v___x_5182_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5192_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5186_ = v___x_5183_;
v_isShared_5187_ = v_isSharedCheck_5192_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5183_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5192_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5188_; lean_object* v___x_5190_; 
v___x_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5188_, 0, v_a_5184_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 0, v___x_5188_);
v___x_5190_ = v___x_5186_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
v_a_5193_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5183_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5183_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5149_);
lean_dec(v_thmName_5147_);
v_a_5202_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5157_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5157_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_thmName_5147_ = stack[0].m_obj;
lean_object* v_levels_5148_ = stack[1].m_obj;
lean_object* v___x_5149_ = stack[2].m_obj;
lean_object* v_____r_5150_ = stack[3].m_obj;
lean_object* v___y_5151_ = stack[4].m_obj;
lean_object* v___y_5152_ = stack[5].m_obj;
lean_object* v___y_5153_ = stack[6].m_obj;
lean_object* v___y_5154_ = stack[7].m_obj;
lean_object* v_res_5210_;
v_res_5210_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5147_, v_levels_5148_, v___x_5149_, v_____r_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
stack->m_obj
 = v_res_5210_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1___boxed(lean_object* v_thmName_5211_, lean_object* v_levels_5212_, lean_object* v___x_5213_, lean_object* v_____r_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5211_, v_levels_5212_, v___x_5213_, v_____r_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
return v_res_5220_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1(void){
_start:
{
lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5222_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__0));
v___x_5223_ = l_Lean_stringToMessageData(v___x_5222_);
return v___x_5223_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3(void){
_start:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = ((lean_object*)(l_Lean_Meta_mkCongrSimpForConst_x3f___closed__2));
v___x_5226_ = l_Lean_stringToMessageData(v___x_5225_);
return v___x_5226_;
}
}
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object* v_declName_5227_, lean_object* v_levels_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_a_5235_; lean_object* v___y_5253_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v_thmName_5260_; lean_object* v___y_5262_; uint8_t v___y_5263_; lean_object* v_a_5291_; lean_object* v___y_5295_; lean_object* v___x_5298_; lean_object* v_env_5299_; uint8_t v___x_5300_; 
v___x_5258_ = lean_obj_once(&l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0, &l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0_once, _init_l_Lean_Meta_mkHCongrWithArityForConst_x3f___closed__0);
v___x_5259_ = ((lean_object*)(l_Lean_Meta_congrSimpSuffix___closed__0));
v_thmName_5260_ = l_Lean_Name_str___override(v_declName_5227_, v___x_5259_);
v___x_5298_ = lean_st_ref_get(v_a_5232_);
v_env_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc_ref(v_env_5299_);
lean_dec(v___x_5298_);
v___x_5300_ = l_Lean_Environment_containsOnBranch(v_env_5299_, v_thmName_5260_);
lean_dec_ref(v_env_5299_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; 
lean_inc(v_thmName_5260_);
v___x_5301_ = l_Lean_executeReservedNameAction(v_thmName_5260_, v_a_5231_, v_a_5232_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
lean_dec_ref_known(v___x_5301_, 1);
v___x_5302_ = lean_box(0);
lean_inc(v_thmName_5260_);
v___x_5303_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5260_, v_levels_5228_, v___x_5258_, v___x_5302_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
v___y_5295_ = v___x_5303_;
goto v___jp_5294_;
}
else
{
lean_object* v_a_5304_; 
lean_dec(v_levels_5228_);
v_a_5304_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5304_);
lean_dec_ref_known(v___x_5301_, 1);
v_a_5291_ = v_a_5304_;
goto v___jp_5290_;
}
}
else
{
lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5305_ = lean_box(0);
lean_inc(v_thmName_5260_);
v___x_5306_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__1(v_thmName_5260_, v_levels_5228_, v___x_5258_, v___x_5305_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
v___y_5295_ = v___x_5306_;
goto v___jp_5294_;
}
v___jp_5234_:
{
if (lean_obj_tag(v_a_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v_a_5235_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v_a_5235_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v_a_5235_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v_a_5235_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5251_; 
v_a_5244_ = lean_ctor_get(v_a_5235_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v_a_5235_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5246_ = v_a_5235_;
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v_a_5235_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5249_; 
if (v_isShared_5247_ == 0)
{
lean_ctor_set_tag(v___x_5246_, 0);
v___x_5249_ = v___x_5246_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5244_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
}
v___jp_5252_:
{
lean_object* v_a_5254_; 
v_a_5254_ = lean_ctor_get(v___y_5253_, 0);
lean_inc(v_a_5254_);
lean_dec_ref(v___y_5253_);
v_a_5235_ = v_a_5254_;
goto v___jp_5234_;
}
v___jp_5255_:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5256_ = lean_box(0);
v___x_5257_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v___x_5256_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
v___y_5253_ = v___x_5257_;
goto v___jp_5252_;
}
v___jp_5261_:
{
if (v___y_5263_ == 0)
{
lean_object* v_toCold_5264_; lean_object* v_options_5265_; uint8_t v_hasTrace_5266_; 
v_toCold_5264_ = lean_ctor_get(v_a_5231_, 0);
v_options_5265_ = lean_ctor_get(v_toCold_5264_, 2);
v_hasTrace_5266_ = lean_ctor_get_uint8(v_options_5265_, sizeof(void*)*1);
if (v_hasTrace_5266_ == 0)
{
lean_dec_ref(v___y_5262_);
lean_dec(v_thmName_5260_);
goto v___jp_5255_;
}
else
{
lean_object* v_inheritedTraceOptions_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; uint8_t v___x_5270_; 
v_inheritedTraceOptions_5267_ = lean_ctor_get(v_toCold_5264_, 11);
v___x_5268_ = ((lean_object*)(l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_));
v___x_5269_ = lean_obj_once(&l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_, &l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_);
v___x_5270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5267_, v_options_5265_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_dec_ref(v___y_5262_);
lean_dec(v_thmName_5260_);
goto v___jp_5255_;
}
else
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5271_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__1);
v___x_5272_ = l_Lean_MessageData_ofName(v_thmName_5260_);
v___x_5273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5271_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
v___x_5274_ = lean_obj_once(&l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3, &l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3_once, _init_l_Lean_Meta_mkCongrSimpForConst_x3f___closed__3);
v___x_5275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5273_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = l_Lean_Exception_toMessageData(v___y_5262_);
v___x_5277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5275_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = l_Lean_addTrace___at___00__private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2__spec__2(v___x_5268_, v___x_5277_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v___x_5280_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_a_5279_);
lean_dec_ref_known(v___x_5278_, 1);
v___x_5280_ = l_Lean_Meta_mkCongrSimpForConst_x3f___lam__0(v_a_5279_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
v___y_5253_ = v___x_5280_;
goto v___jp_5252_;
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
v_a_5281_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5278_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5278_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
}
else
{
lean_object* v___x_5289_; 
lean_dec(v_thmName_5260_);
v___x_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___y_5262_);
return v___x_5289_;
}
}
v___jp_5290_:
{
uint8_t v___x_5292_; 
v___x_5292_ = l_Lean_Exception_isInterrupt(v_a_5291_);
if (v___x_5292_ == 0)
{
uint8_t v___x_5293_; 
lean_inc_ref(v_a_5291_);
v___x_5293_ = l_Lean_Exception_isRuntime(v_a_5291_);
v___y_5262_ = v_a_5291_;
v___y_5263_ = v___x_5293_;
goto v___jp_5261_;
}
else
{
v___y_5262_ = v_a_5291_;
v___y_5263_ = v___x_5292_;
goto v___jp_5261_;
}
}
v___jp_5294_:
{
if (lean_obj_tag(v___y_5295_) == 0)
{
lean_object* v_a_5296_; 
lean_dec(v_thmName_5260_);
v_a_5296_ = lean_ctor_get(v___y_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___y_5295_, 1);
v_a_5235_ = v_a_5296_;
goto v___jp_5234_;
}
else
{
lean_object* v_a_5297_; 
v_a_5297_ = lean_ctor_get(v___y_5295_, 0);
lean_inc(v_a_5297_);
lean_dec_ref_known(v___y_5295_, 1);
v_a_5291_ = v_a_5297_;
goto v___jp_5290_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkCongrSimpForConst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_5227_ = stack[0].m_obj;
lean_object* v_levels_5228_ = stack[1].m_obj;
lean_object* v_a_5229_ = stack[2].m_obj;
lean_object* v_a_5230_ = stack[3].m_obj;
lean_object* v_a_5231_ = stack[4].m_obj;
lean_object* v_a_5232_ = stack[5].m_obj;
lean_object* v_res_5307_;
v_res_5307_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5227_, v_levels_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
stack->m_obj
 = v_res_5307_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f___boxed(lean_object* v_declName_5308_, lean_object* v_levels_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_5308_, v_levels_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_);
lean_dec(v_a_5313_);
lean_dec_ref(v_a_5312_);
lean_dec(v_a_5311_);
lean_dec_ref(v_a_5310_);
return v_res_5315_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCongrArgKind_default = _init_l_Lean_Meta_instInhabitedCongrArgKind_default();
l_Lean_Meta_instInhabitedCongrArgKind = _init_l_Lean_Meta_instInhabitedCongrArgKind();
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_3482611248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_118617060____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_congrKindsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_congrKindsExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_1395845979____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CongrTheorems_0__Lean_Meta_initFn_00___x40_Lean_Meta_CongrTheorems_4172217453____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CongrTheorems(builtin);
}
#ifdef __cplusplus
}
#endif
